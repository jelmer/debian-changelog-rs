//! A lossless parser for Debian changelog files.
//!
//! As documented in Debian Policy:
//! https://www.debian.org/doc/debian-policy/ch-source.html#debian-changelog-debian-changelog
//!
//! Example:
//!
//! ```rust
//! use std::io::Read;
//! let contents = r#"rustc (1.70.0+dfsg1-1) unstable; urgency=medium
//!
//!   * Upload to unstable
//!
//!  -- Fabian Grünbichler <debian@fabian.gruenbichler.email>  Wed, 20 Sep 2023 20:18:40 +0200
//! "#;
//! let changelog: debian_changelog::ChangeLog = contents.parse().unwrap();
//! assert_eq!(
//!     vec![("rustc".to_string(), "1.70.0+dfsg1-1".parse().unwrap())],
//!     changelog.entries().map(
//!         |e| (e.package().unwrap(), e.version().unwrap()))
//!     .collect::<Vec<_>>());
//! ```

mod lex;
mod parse;
use lazy_regex::regex_captures;

pub use crate::parse::{Error, ParseError};

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

pub fn get_maintainer_from_env(
    get_env: impl Fn(&str) -> Option<String>,
) -> Option<(String, String)> {
    use nix::unistd;
    use std::io::BufRead;

    let mut debemail = get_env("DEBEMAIL");
    let mut debfullname = get_env("DEBFULLNAME");

    // Split email and name
    if let Some(email) = debemail.as_ref() {
        if let Some((_, name, email)) = regex_captures!(r"^(.*)\s+<(.*)>$", email.as_str()) {
            if debfullname.is_none() {
                debfullname = Some(name.to_string());
            }
            debemail = Some(email.to_string());
        }
    }
    if debfullname.is_none() || debemail.is_none() {
        if let Some(email) = get_env("EMAIL") {
            if let Some((_, name, email)) = regex_captures!(r"^(.*)\s+<(.*)>$", email.as_str()) {
                if debfullname.is_none() {
                    debfullname = Some(name.to_string());
                }
                debemail = Some(email.to_string());
            }
        }
    }

    // Get maintainer's name
    let maintainer = if let Some(m) = debfullname {
        Some(m.trim().to_string())
    } else if let Some(m) = get_env("NAME") {
        Some(m.trim().to_string())
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
    let email_address = if let Some(email) = debemail {
        Some(email)
    } else if let Some(email) = get_env("EMAIL") {
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

    if let (Some(maintainer), Some(email_address)) = (maintainer, email_address) {
        Some((maintainer, email_address))
    } else {
        None
    }
}

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
pub fn get_maintainer() -> Option<(String, String)> {
    get_maintainer_from_env(|s| std::env::var(s).ok())
}

#[cfg(test)]
mod get_maintainer_from_env_tests {
    use super::*;

    #[test]
    fn test_normal() {
        get_maintainer();
    }

    #[test]
    fn test_deb_vars() {
        let mut d = std::collections::HashMap::new();
        d.insert("DEBFULLNAME".to_string(), "Jelmer".to_string());
        d.insert("DEBEMAIL".to_string(), "jelmer@example.com".to_string());
        let t = get_maintainer_from_env(|s| d.get(s).cloned());
        assert_eq!(
            Some(("Jelmer".to_string(), "jelmer@example.com".to_string())),
            t
        );
    }

    #[test]
    fn test_email_var() {
        let mut d = std::collections::HashMap::new();
        d.insert("NAME".to_string(), "Jelmer".to_string());
        d.insert("EMAIL".to_string(), "foo@example.com".to_string());
        let t = get_maintainer_from_env(|s| d.get(s).cloned());
        assert_eq!(
            Some(("Jelmer".to_string(), "foo@example.com".to_string())),
            t
        );
    }
}
