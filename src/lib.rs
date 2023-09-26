mod lex;
mod parse;
use lazy_regex::regex_captures;

/// See https://manpages.debian.org/bookworm/dpkg-dev/deb-changelog.5.en.html

/// Let's start with defining all kinds of tokens and
/// composite nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub enum SyntaxKind {
    IDENTIFIER = 0,
    INDENT,
    TEXT,
    WHITESPACE,
    VERSION,   // "(3.3.4-1)"
    SEMICOLON, // ";"
    EQUALS,    // "="
    DETAIL,    // "* New upstream release."
    NEWLINE,   // newlines are explicit
    ERROR,     // as well as errors
    COMMENT,   // "#"

    // composite nodes
    ROOT,  // The entire file
    ENTRY, // A single entry
    ENTRY_HEADER,
    ENTRY_FOOTER,
    METADATA,
    METADATA_ENTRY,
    METADATA_KEY,
    METADATA_VALUE,
    ENTRY_BODY,
    DISTRIBUTIONS,
    EMPTY_LINE,

    TIMESTAMP,
    MAINTAINER,
    EMAIL,
}

/// Convert our `SyntaxKind` into the rowan `SyntaxKind`.
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

pub use crate::parse::{ChangeLog, Entry};

/// Get the maintainer information in the same manner as dch.
///
/// This function gets the information about the current user for
/// the maintainer field using environment variables of gecos
/// information as appropriate.
///
/// It uses the same algorithm as dch to get the information, namely
/// DEBEMAIL, DEBFULLNAME, EMAIL, NAME, /etc/mailname and gecos.
///
/// # Returns
///
/// a tuple of the full name, email pair as strings.
///     Either of the pair may be None if that value couldn't
///     be determined.
pub fn get_maintainer() -> (Option<String>, Option<String>) {
    use nix::unistd;
    use std::io::BufRead;
    // Split email and name
    if let Ok(debemail) = std::env::var("DEBEMAIL") {
        if let Some((_, _name, email)) = regex_captures!(r"^(.*)\s+<(.*)>$", debemail.as_str()) {
            if let Ok(name) = std::env::var("DEBFULLNAME") {
                std::env::set_var("DEBFULLNAME", name);
            }
            std::env::set_var("DEBEMAIL", email);
        }
    }
    if std::env::var("DEBFULLNAME").is_err() || std::env::var("DEBEMAIL").is_err() {
        if let Ok(email) = std::env::var("EMAIL") {
            if let Some((_, name, email)) = regex_captures!(r"^(.*)\s+<(.*)>$", email.as_str()) {
                if std::env::var("DEBFULLNAME").is_err() {
                    std::env::set_var("DEBFULLNAME", name);
                }
                std::env::set_var("DEBEMAIL", email);
            }
        }
    }

    // Get maintainer's name
    let maintainer = if let Ok(m) = std::env::var("DEBFULLNAME") {
        Some(m)
    } else if let Ok(m) = std::env::var("NAME") {
        Some(m)
    } else {
        // Use password database if no data in environment variables
        match unistd::User::from_uid(unistd::getuid()) {
            Ok(Some(user)) => {
                if let Ok(gecos) = user.gecos.to_str() {
                    let mut parts = gecos.split(',');
                    parts.next().map(|name_part| name_part.to_string())
                } else {
                    None
                }
            }
            Ok(None) => {
                // Hmm, user doesn't exist?
                None
            }
            Err(e) => {
                log::error!("Error getting information for current user: {}", e);
                None
            }
        }
    };

    // Get maintainer's mail address
    let email_address = if let Ok(email) = std::env::var("DEBEMAIL") {
        Some(email)
    } else if let Ok(email) = std::env::var("EMAIL") {
        Some(email)
    } else {
        // Read /etc/mailname or use hostname
        let mut addr: Option<String> = None;

        if let Ok(mailname_file) = std::fs::File::open("/etc/mailname") {
            let mut reader = std::io::BufReader::new(mailname_file);
            if let Ok(line) = reader.fill_buf() {
                if !line.is_empty() {
                    addr = Some(String::from_utf8_lossy(line).trim().to_string());
                }
            }
        }

        if addr.is_none() {
            if let Ok(hostname) = nix::unistd::gethostname() {
                if let Some(host) = hostname.to_str() {
                    addr = Some(host.to_string());
                }
            }
        }

        if let Some(hostname) = addr {
            match unistd::User::from_uid(unistd::getuid()) {
                Ok(Some(user)) => Some(format!("{}@{}", user.name, hostname)),
                Ok(None) => {
                    // Hmm, user doesn't exist?
                    None
                }
                Err(e) => {
                    log::error!("Error getting information for current user: {}", e);
                    None
                }
            }
        } else {
            None
        }
    };

    (maintainer, email_address)
}
