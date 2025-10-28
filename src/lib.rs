#![deny(missing_docs)]
//! A lossless parser for Debian changelog files.
//!
//! See https://manpages.debian.org/bookworm/dpkg-dev/deb-changelog.5.en.html
//!
//! For its format specification, see [Debian Policy](https://www.debian.org/doc/debian-policy/ch-source.html#debian-changelog-debian-changelog).
//!
//! Example:
//!
//! ```rust
//! use std::io::Read;
//! let contents = r#"rustc (1.70.0+dfsg1-1) unstable; urgency=medium
//!
//!   * Upload to unstable
//!
//!  -- Jelmer Vernooĳ <jelmer@debian.org>  Wed, 20 Sep 2023 20:18:40 +0200
//! "#;
//! let changelog: debian_changelog::ChangeLog = contents.parse().unwrap();
//! assert_eq!(
//!     vec![("rustc".to_string(), "1.70.0+dfsg1-1".parse().unwrap())],
//!     changelog.iter().map(
//!         |e| (e.package().unwrap(), e.version().unwrap()))
//!     .collect::<Vec<_>>());
//! ```

mod lex;
mod parse;
use lazy_regex::regex_captures;
pub mod changes;
pub mod textwrap;
use crate::parse::{SyntaxNode, SyntaxToken};
use debversion::Version;
use rowan::ast::AstNode;

pub use crate::changes::changes_by_author;
pub use crate::parse::{ChangeLog, Entry, Error, Parse, ParseError, Urgency};

/// Represents a logical change within a changelog entry.
///
/// This struct wraps specific DETAIL tokens within an Entry's syntax tree
/// and provides methods to manipulate them while maintaining the AST structure.
#[derive(Debug, Clone)]
pub struct Change {
    /// The parent entry containing this change
    entry: Entry,
    /// The author of the change (if attributed)
    author: Option<String>,
    /// Line numbers in the original entry where this change appears
    line_numbers: Vec<usize>,
    /// The actual change lines as tokens in the syntax tree
    detail_tokens: Vec<SyntaxToken>,
}

impl Change {
    /// Create a new Change instance.
    pub(crate) fn new(
        entry: Entry,
        author: Option<String>,
        line_numbers: Vec<usize>,
        detail_tokens: Vec<SyntaxToken>,
    ) -> Self {
        Self {
            entry,
            author,
            line_numbers,
            detail_tokens,
        }
    }

    /// Get the author of this change.
    pub fn author(&self) -> Option<&str> {
        self.author.as_deref()
    }

    /// Get the lines of this change.
    pub fn lines(&self) -> Vec<String> {
        self.detail_tokens
            .iter()
            .map(|token| token.text().to_string())
            .collect()
    }

    /// Get the package name this change belongs to.
    pub fn package(&self) -> Option<String> {
        self.entry.package()
    }

    /// Get the version this change belongs to.
    pub fn version(&self) -> Option<Version> {
        self.entry.version()
    }

    /// Check if this change is attributed to a specific author.
    pub fn is_attributed(&self) -> bool {
        self.author.is_some()
    }

    /// Get a reference to the parent entry.
    pub fn entry(&self) -> &Entry {
        &self.entry
    }

    /// Remove this change from its parent entry.
    ///
    /// This removes all DETAIL tokens (ENTRY_BODY nodes) associated with this change
    /// from the syntax tree.
    pub fn remove(self) {
        // Collect the parent ENTRY_BODY nodes that contain our detail tokens
        let mut body_nodes_to_remove = Vec::new();

        for token in &self.detail_tokens {
            if let Some(parent) = token.parent() {
                if parent.kind() == SyntaxKind::ENTRY_BODY {
                    // Check if we haven't already marked this node for removal
                    if !body_nodes_to_remove.iter().any(|n: &SyntaxNode| n == &parent) {
                        body_nodes_to_remove.push(parent);
                    }
                }
            }
        }

        // Remove the ENTRY_BODY nodes from the entry's syntax tree
        for body_node in body_nodes_to_remove {
            let index = body_node.index();
            self.entry.syntax().splice_children(index..index + 1, vec![]);
        }
    }

    /// Replace this change with new lines.
    ///
    /// This removes the current change lines and replaces them with the provided lines.
    ///
    /// # Arguments
    /// * `new_lines` - The new change lines to replace with (e.g., `["* Updated feature"]`)
    pub fn replace_with(&self, new_lines: Vec<&str>) {
        use rowan::GreenNodeBuilder;

        // Find the first ENTRY_BODY node to determine insertion point
        let first_body_node = self.detail_tokens.first()
            .and_then(|token| token.parent())
            .filter(|parent| parent.kind() == SyntaxKind::ENTRY_BODY);

        if let Some(first_node) = first_body_node {
            let insert_index = first_node.index();

            // Collect all ENTRY_BODY nodes to remove
            let mut body_nodes_to_remove = Vec::new();
            for token in &self.detail_tokens {
                if let Some(parent) = token.parent() {
                    if parent.kind() == SyntaxKind::ENTRY_BODY {
                        if !body_nodes_to_remove.iter().any(|n: &SyntaxNode| n == &parent) {
                            body_nodes_to_remove.push(parent);
                        }
                    }
                }
            }

            // Build replacement nodes
            let mut new_nodes = Vec::new();
            for line in new_lines {
                let mut builder = GreenNodeBuilder::new();
                builder.start_node(SyntaxKind::ENTRY_BODY.into());
                if !line.is_empty() {
                    builder.token(SyntaxKind::INDENT.into(), "  ");
                    builder.token(SyntaxKind::DETAIL.into(), line);
                }
                builder.token(SyntaxKind::NEWLINE.into(), "\n");
                builder.finish_node();

                let syntax = SyntaxNode::new_root_mut(builder.finish());
                new_nodes.push(syntax.into());
            }

            // Remove old nodes and insert new ones
            // We need to remove from highest index to lowest to avoid index shifting issues
            let mut sorted_nodes = body_nodes_to_remove.clone();
            sorted_nodes.sort_by_key(|n| std::cmp::Reverse(n.index()));

            for (i, node) in sorted_nodes.iter().enumerate() {
                let idx = node.index();
                if i == 0 {
                    // For the first removal, insert the new nodes
                    self.entry.syntax().splice_children(idx..idx + 1, new_nodes.clone());
                } else {
                    // For subsequent removals, just remove
                    self.entry.syntax().splice_children(idx..idx + 1, vec![]);
                }
            }
        }
    }
}

/// Let's start with defining all kinds of tokens and
/// composite nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
#[allow(missing_docs)]
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

/// Parse a identity string
///
/// # Arguments
/// * `s` - The string to parse
///
/// # Returns
/// A tuple with name and email address
pub fn parseaddr(s: &str) -> (Option<&str>, &str) {
    if let Some((_, name, email)) = regex_captures!(r"^(.*)\s+<(.*)>$", s) {
        if name.is_empty() {
            (None, email)
        } else {
            (Some(name), email)
        }
    } else {
        (None, s)
    }
}

/// Get the maintainer information from the environment.
pub fn get_maintainer_from_env(
    get_env: impl Fn(&str) -> Option<String>,
) -> Option<(String, String)> {
    use std::io::BufRead;

    let mut debemail = get_env("DEBEMAIL");
    let mut debfullname = get_env("DEBFULLNAME");

    // Split email and name
    if let Some(email) = debemail.as_ref() {
        let (parsed_name, parsed_email) = parseaddr(email);
        if let Some(parsed_name) = parsed_name {
            if debfullname.is_none() {
                debfullname = Some(parsed_name.to_string());
            }
        }
        debemail = Some(parsed_email.to_string());
    }
    if debfullname.is_none() || debemail.is_none() {
        if let Some(email) = get_env("EMAIL") {
            let (parsed_name, parsed_email) = parseaddr(email.as_str());
            if let Some(parsed_name) = parsed_name {
                if debfullname.is_none() {
                    debfullname = Some(parsed_name.to_string());
                }
            }
            debemail = Some(parsed_email.to_string());
        }
    }

    // Get maintainer's name
    let maintainer = if let Some(m) = debfullname {
        Some(m.trim().to_string())
    } else if let Some(m) = get_env("NAME") {
        Some(m.trim().to_string())
    } else {
        Some(whoami::realname())
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
            match whoami::fallible::hostname() {
                Ok(hostname) => {
                    addr = Some(hostname);
                }
                Err(e) => {
                    log::debug!("Failed to get hostname: {}", e);
                    addr = None;
                }
            }
        }

        addr.map(|hostname| format!("{}@{}", whoami::username(), hostname))
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

/// Simple representation of an identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identity {
    /// Name of the maintainer
    pub name: String,

    /// Email address of the maintainer
    pub email: String,
}

impl Identity {
    /// Create a new identity.
    pub fn new(name: String, email: String) -> Self {
        Self { name, email }
    }

    /// Get the maintainer information from the environment.
    pub fn from_env() -> Option<Self> {
        get_maintainer().map(|(name, email)| Self { name, email })
    }
}

impl From<(String, String)> for Identity {
    fn from((name, email): (String, String)) -> Self {
        Self { name, email }
    }
}

impl std::fmt::Display for Identity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} <{}>", self.name, self.email)
    }
}

/// Constant for the unreleased distribution name
pub const UNRELEASED: &str = "UNRELEASED";
/// Prefix for unreleased distribution variants
const UNRELEASED_PREFIX: &str = "UNRELEASED-";

/// Check if the given distribution marks an unreleased entry.
pub fn distribution_is_unreleased(distribution: &str) -> bool {
    distribution == UNRELEASED || distribution.starts_with(UNRELEASED_PREFIX)
}

/// Check if any of the given distributions marks an unreleased entry.
pub fn distributions_is_unreleased(distributions: &[&str]) -> bool {
    distributions.iter().any(|x| distribution_is_unreleased(x))
}

#[test]
fn test_distributions_is_unreleased() {
    assert!(distributions_is_unreleased(&["UNRELEASED"]));
    assert!(distributions_is_unreleased(&[
        "UNRELEASED-1",
        "UNRELEASED-2"
    ]));
    assert!(distributions_is_unreleased(&["UNRELEASED", "UNRELEASED-2"]));
    assert!(!distributions_is_unreleased(&["stable"]));
}

/// Check whether this is a traditional inaugural release
pub fn is_unreleased_inaugural(cl: &ChangeLog) -> bool {
    let mut entries = cl.iter();
    if let Some(entry) = entries.next() {
        if entry.is_unreleased() == Some(false) {
            return false;
        }
        let changes = entry.change_lines().collect::<Vec<_>>();
        if changes.len() > 1 || !changes[0].starts_with("* Initial release") {
            return false;
        }
        entries.next().is_none()
    } else {
        false
    }
}

#[cfg(test)]
mod is_unreleased_inaugural_tests {
    use super::*;

    #[test]
    fn test_empty() {
        assert!(!is_unreleased_inaugural(&ChangeLog::new()));
    }

    #[test]
    fn test_unreleased_inaugural() {
        let mut cl = ChangeLog::new();
        cl.new_entry()
            .maintainer(("Jelmer Vernooĳ".into(), "jelmer@debian.org".into()))
            .distribution(UNRELEASED.to_string())
            .version("1.0.0".parse().unwrap())
            .change_line("* Initial release".to_string())
            .finish();
        assert!(is_unreleased_inaugural(&cl));
    }

    #[test]
    fn test_not_unreleased_inaugural() {
        let mut cl = ChangeLog::new();
        cl.new_entry()
            .maintainer(("Jelmer Vernooĳ".into(), "jelmer@debian.org".into()))
            .distributions(vec!["unstable".to_string()])
            .version("1.0.0".parse().unwrap())
            .change_line("* Initial release".to_string())
            .finish();
        assert_eq!(cl.iter().next().unwrap().is_unreleased(), Some(false));

        // Not unreleased
        assert!(!is_unreleased_inaugural(&cl));

        cl.new_entry()
            .maintainer(("Jelmer Vernooĳ".into(), "jelmer@debian.org".into()))
            .distribution(UNRELEASED.to_string())
            .version("1.0.1".parse().unwrap())
            .change_line("* Some change".to_string())
            .finish();
        // Not inaugural
        assert!(!is_unreleased_inaugural(&cl));
    }
}

const DEFAULT_DISTRIBUTION: &[&str] = &[UNRELEASED];

/// Create a release for a changelog file.
///
/// # Arguments
/// * `cl` - The changelog to release
/// * `distribution` - The distribution to release to. If None, the distribution
///   of the previous entry is used.
/// * `timestamp` - The timestamp to use for the release. If None, the current time is used.
/// * `maintainer` - The maintainer to use for the release. If None, the maintainer
///   is extracted from the environment.
///
/// # Returns
/// Whether a release was created.
pub fn release(
    cl: &mut ChangeLog,
    distribution: Option<Vec<String>>,
    timestamp: Option<chrono::DateTime<chrono::FixedOffset>>,
    maintainer: Option<(String, String)>,
) -> bool {
    let mut entries = cl.iter();
    let mut first_entry = entries.next().unwrap();
    let second_entry = entries.next();
    let distribution = distribution.unwrap_or_else(|| {
        // Inherit from previous entry
        second_entry
            .and_then(|e| e.distributions())
            .unwrap_or_else(|| {
                DEFAULT_DISTRIBUTION
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
            })
    });
    if first_entry.is_unreleased() == Some(false) {
        take_uploadership(&mut first_entry, maintainer);
        first_entry.set_distributions(distribution);
        let timestamp = timestamp.unwrap_or(chrono::offset::Utc::now().into());
        first_entry.set_datetime(timestamp);
        true
    } else {
        false
    }
}

/// Take uploadership of a changelog entry, but attribute contributors.
///
/// # Arguments
/// * `entry` - Changelog entry to modify
/// * `maintainer` - Tuple with (name, email) of maintainer to take ownership
pub fn take_uploadership(entry: &mut Entry, maintainer: Option<(String, String)>) {
    let (maintainer_name, maintainer_email) = if let Some(m) = maintainer {
        m
    } else {
        get_maintainer().unwrap()
    };
    if let (Some(current_maintainer), Some(current_email)) = (entry.maintainer(), entry.email()) {
        if current_maintainer != maintainer_name || current_email != maintainer_email {
            if let Some(first_line) = entry.change_lines().next() {
                if first_line.starts_with("[ ") {
                    entry.prepend_change_line(
                        crate::changes::format_section_title(current_maintainer.as_str()).as_str(),
                    );
                }
            }
        }
    }
    entry.set_maintainer((maintainer_name, maintainer_email));
}

/// Update changelog with commit messages from commits
pub fn gbp_dch(path: &std::path::Path) -> std::result::Result<(), std::io::Error> {
    // Run the "gbp dch" command with working copy at `path`
    let output = std::process::Command::new("gbp")
        .arg("dch")
        .arg("--ignore-branch")
        .current_dir(path)
        .output()?;

    if !output.status.success() {
        return Err(std::io::Error::other(format!(
            "gbp dch failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }

    Ok(())
}

/// Iterator over changelog entries grouped by author (maintainer).
///
/// This function returns an iterator that groups changelog entries by their maintainer
/// (author), similar to debmutate.changelog functionality.
///
/// # Arguments
/// * `changelog` - The changelog to iterate over
///
/// # Returns
/// An iterator over tuples of (author_name, author_email, Vec<Entry>)
pub fn iter_entries_by_author(
    changelog: &ChangeLog,
) -> impl Iterator<Item = (String, String, Vec<Entry>)> + '_ {
    use std::collections::BTreeMap;

    let mut grouped: BTreeMap<(String, String), Vec<Entry>> = BTreeMap::new();

    for entry in changelog.iter() {
        let maintainer_name = entry.maintainer().unwrap_or_else(|| "Unknown".to_string());
        let maintainer_email = entry
            .email()
            .unwrap_or_else(|| "unknown@unknown".to_string());
        let key = (maintainer_name, maintainer_email);

        grouped.entry(key).or_insert_with(Vec::new).push(entry);
    }

    grouped
        .into_iter()
        .map(|((name, email), entries)| (name, email, entries))
}

/// Iterator over all changes across all entries, grouped by author.
///
/// This function iterates through all entries in a changelog and returns changes
/// grouped by their attributed authors, including those in author sections like [ Author Name ].
///
/// # Arguments
/// * `changelog` - The changelog to iterate over
///
/// # Returns
/// A vector of Change objects that can be manipulated or filtered
pub fn iter_changes_by_author(changelog: &ChangeLog) -> Vec<Change> {
    let mut result = Vec::new();

    for entry in changelog.iter() {
        let changes: Vec<String> = entry.change_lines().map(|s| s.to_string()).collect();

        // Collect all DETAIL tokens from the entry with their text
        let all_detail_tokens: Vec<SyntaxToken> = entry
            .syntax()
            .children()
            .flat_map(|n| {
                n.children_with_tokens()
                    .filter_map(|it| it.as_token().cloned())
                    .filter(|token| token.kind() == SyntaxKind::DETAIL)
            })
            .collect();

        for (author, linenos, lines) in
            crate::changes::changes_by_author(changes.iter().map(|s| s.as_str()))
        {
            let author_name = author.map(|s| s.to_string());

            // Extract the specific DETAIL tokens for this change by matching text content
            let detail_tokens: Vec<SyntaxToken> = lines
                .iter()
                .filter_map(|line_text| {
                    all_detail_tokens
                        .iter()
                        .find(|token| token.text() == *line_text)
                        .cloned()
                })
                .collect();

            let change = Change::new(entry.clone(), author_name, linenos, detail_tokens);
            result.push(change);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parseaddr() {
        assert_eq!(
            (Some("Jelmer"), "jelmer@jelmer.uk"),
            parseaddr("Jelmer <jelmer@jelmer.uk>")
        );
        assert_eq!((None, "jelmer@jelmer.uk"), parseaddr("jelmer@jelmer.uk"));
    }

    #[test]
    fn test_parseaddr_empty() {
        assert_eq!((None, ""), parseaddr(""));
    }

    #[test]
    fn test_release_already_released() {
        use crate::parse::ChangeLog;

        let mut changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let result = release(
            &mut changelog,
            Some(vec!["unstable".to_string()]),
            None,
            None,
        );

        // The function returns true if the entry is NOT unreleased (already released)
        assert!(result);
    }

    #[test]
    fn test_release_unreleased() {
        use crate::parse::ChangeLog;

        let mut changelog: ChangeLog = r#"breezy (3.3.4-1) UNRELEASED; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let result = release(
            &mut changelog,
            Some(vec!["unstable".to_string()]),
            None,
            Some(("Test User".to_string(), "test@example.com".to_string())),
        );

        // The function returns false if the entry is unreleased
        assert!(!result);
    }

    #[test]
    fn test_take_uploadership_same_maintainer() {
        use crate::parse::ChangeLog;

        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Test User <test@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let mut entries: Vec<Entry> = changelog.into_iter().collect();
        take_uploadership(
            &mut entries[0],
            Some(("Test User".to_string(), "test@example.com".to_string())),
        );

        // Should not add author section when maintainer is the same
        assert!(!entries[0].to_string().contains("[ Test User ]"));
    }

    #[test]
    fn test_take_uploadership_different_maintainer() {
        use crate::parse::ChangeLog;

        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Original User <original@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let mut entries: Vec<Entry> = changelog.into_iter().collect();

        take_uploadership(
            &mut entries[0],
            Some(("New User".to_string(), "new@example.com".to_string())),
        );

        // The take_uploadership function updates the maintainer in the footer
        assert!(entries[0]
            .to_string()
            .contains("New User <new@example.com>"));
        assert_eq!(entries[0].email(), Some("new@example.com".to_string()));
    }

    #[test]
    fn test_identity_display() {
        let identity = Identity {
            name: "Test User".to_string(),
            email: "test@example.com".to_string(),
        };
        assert_eq!(identity.to_string(), "Test User <test@example.com>");

        let identity_empty_name = Identity {
            name: "".to_string(),
            email: "test@example.com".to_string(),
        };
        assert_eq!(identity_empty_name.to_string(), " <test@example.com>");
    }

    #[test]
    fn test_gbp_dch_failure() {
        // Test with invalid path that would cause gbp dch to fail
        let result = gbp_dch(std::path::Path::new("/nonexistent/path"));
        assert!(result.is_err());
    }

    #[test]
    fn test_iter_entries_by_author() {
        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500

breezy (3.3.3-1) unstable; urgency=low

  * Bug fix release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Sun, 03 Sep 2023 17:12:30 -0500

breezy (3.3.2-1) unstable; urgency=low

  * Another release.

 -- Jane Doe <jane@example.com>  Sat, 02 Sep 2023 16:11:15 -0500
"#
        .parse()
        .unwrap();

        let authors: Vec<(String, String, Vec<Entry>)> =
            iter_entries_by_author(&changelog).collect();

        assert_eq!(authors.len(), 2);
        assert_eq!(authors[0].0, "Jane Doe");
        assert_eq!(authors[0].1, "jane@example.com");
        assert_eq!(authors[0].2.len(), 1);
        assert_eq!(authors[1].0, "Jelmer Vernooĳ");
        assert_eq!(authors[1].1, "jelmer@debian.org");
        assert_eq!(authors[1].2.len(), 2);
    }

    #[test]
    fn test_iter_changes_by_author() {
        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  [ Author 1 ]
  * Change by Author 1

  [ Author 2 ]
  * Change by Author 2

  * Unattributed change

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let changes = iter_changes_by_author(&changelog);

        assert_eq!(changes.len(), 3);

        // First change attributed to Author 1
        assert_eq!(changes[0].author(), Some("Author 1"));
        assert_eq!(changes[0].package(), Some("breezy".to_string()));
        assert_eq!(changes[0].lines(), vec!["* Change by Author 1"]);

        // Second change attributed to Author 2
        assert_eq!(changes[1].author(), Some("Author 2"));
        assert_eq!(changes[1].package(), Some("breezy".to_string()));
        assert_eq!(changes[1].lines(), vec!["* Change by Author 2"]);

        // Third change unattributed
        assert_eq!(changes[2].author(), None);
        assert_eq!(changes[2].package(), Some("breezy".to_string()));
        assert_eq!(changes[2].lines(), vec!["* Unattributed change"]);
    }

    #[test]
    fn test_change_remove() {
        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  [ Author 1 ]
  * Change by Author 1

  [ Author 2 ]
  * Change by Author 2

  * Unattributed change

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#.parse().unwrap();

        let changes = iter_changes_by_author(&changelog);
        assert_eq!(changes.len(), 3);

        // Remove the second change (Author 2)
        changes[1].clone().remove();

        // Re-read the changes
        let remaining_changes = iter_changes_by_author(&changelog);

        // The Author 2 section header remains but with no changes,
        // so it will show up as an empty change for Author 2,
        // followed by the unattributed change
        assert_eq!(remaining_changes.len(), 2);

        // Should have Author 1 and Author 2 (but with no lines)
        assert_eq!(remaining_changes[0].author(), Some("Author 1"));
        assert_eq!(remaining_changes[0].lines(), vec!["* Change by Author 1"]);

        // Author 2's section header remains but the change is removed
        assert_eq!(remaining_changes[1].author(), Some("Author 2"));
        assert_eq!(remaining_changes[1].lines(), vec!["* Unattributed change"]);
    }

    #[test]
    fn test_change_replace_with() {
        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  [ Author 1 ]
  * Change by Author 1

  [ Author 2 ]
  * Change by Author 2

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#.parse().unwrap();

        let changes = iter_changes_by_author(&changelog);
        assert_eq!(changes.len(), 2);

        // Replace Author 2's change
        changes[1].replace_with(vec!["* Updated change by Author 2", "* Another line"]);

        // Re-read the changes
        let updated_changes = iter_changes_by_author(&changelog);
        assert_eq!(updated_changes.len(), 2);

        // Author 1's change should be unchanged
        assert_eq!(updated_changes[0].author(), Some("Author 1"));
        assert_eq!(updated_changes[0].lines(), vec!["* Change by Author 1"]);

        // Author 2's change should be replaced
        assert_eq!(updated_changes[1].author(), Some("Author 2"));
        assert_eq!(updated_changes[1].lines(), vec!["* Updated change by Author 2", "* Another line"]);
    }

    #[test]
    fn test_change_replace_with_single_line() {
        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * Old change

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#.parse().unwrap();

        let changes = iter_changes_by_author(&changelog);
        assert_eq!(changes.len(), 1);

        // Replace with a new single line
        changes[0].replace_with(vec!["* New change"]);

        // Re-read the changes
        let updated_changes = iter_changes_by_author(&changelog);
        assert_eq!(updated_changes.len(), 1);
        assert_eq!(updated_changes[0].lines(), vec!["* New change"]);
    }
}
