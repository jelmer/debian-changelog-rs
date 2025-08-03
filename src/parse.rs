use crate::lex::lex;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use chrono::{DateTime, FixedOffset};
use debversion::Version;
use rowan::ast::AstNode;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
/// Urgency of the changes in the changelog entry
pub enum Urgency {
    #[default]
    /// Low urgency
    Low,

    /// Medium urgency
    Medium,

    /// High urgency
    High,

    /// Emergency urgency
    Emergency,

    /// Critical urgency
    Critical,
}

impl std::fmt::Display for Urgency {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Urgency::Low => f.write_str("low"),
            Urgency::Medium => f.write_str("medium"),
            Urgency::High => f.write_str("high"),
            Urgency::Emergency => f.write_str("emergency"),
            Urgency::Critical => f.write_str("critical"),
        }
    }
}

impl FromStr for Urgency {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "low" => Ok(Urgency::Low),
            "medium" => Ok(Urgency::Medium),
            "high" => Ok(Urgency::High),
            "emergency" => Ok(Urgency::Emergency),
            "critical" => Ok(Urgency::Critical),
            _ => Err(ParseError(vec![format!("invalid urgency: {}", s)])),
        }
    }
}

#[derive(Debug)]
/// Error while reading a changelog file.
pub enum Error {
    /// I/O Error
    Io(std::io::Error),

    /// Parsing error
    Parse(ParseError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Error::Io(e) => write!(f, "IO error: {}", e),
            Error::Parse(e) => write!(f, "Parse error: {}", e),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io(e)
    }
}

impl std::error::Error for Error {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Error while parsing
pub struct ParseError(Vec<String>);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for err in &self.0 {
            writeln!(f, "{}", err)?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

/// Second, implementing the `Language` trait teaches rowan to convert between
/// these two SyntaxKind types, allowing for a nicer SyntaxNode API where
/// "kinds" are values from our `enum SyntaxKind`, instead of plain u16 values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// GreenNode is an immutable tree, which is cheap to change,
/// but doesn't contain offsets and parent pointers.
use rowan::{GreenNode, GreenToken};

/// You can construct GreenNodes by hand, but a builder
/// is helpful for top-down parsers: it maintains a stack
/// of currently in-progress nodes
use rowan::GreenNodeBuilder;

/// The result of parsing: a syntax tree and a collection of errors.
///
/// This type is designed to be stored in Salsa databases as it contains
/// the thread-safe `GreenNode` instead of the non-thread-safe `SyntaxNode`.
#[derive(Debug)]
pub struct Parse<T> {
    green: GreenNode,
    errors: Vec<String>,
    _ty: std::marker::PhantomData<T>,
}

// The T parameter is only used as a phantom type, so we can implement Clone and PartialEq
// without requiring T to implement them
impl<T> Clone for Parse<T> {
    fn clone(&self) -> Self {
        Parse {
            green: self.green.clone(),
            errors: self.errors.clone(),
            _ty: std::marker::PhantomData,
        }
    }
}

impl<T> PartialEq for Parse<T> {
    fn eq(&self, other: &Self) -> bool {
        self.green == other.green && self.errors == other.errors
    }
}

impl<T> Eq for Parse<T> {}

// Implement Send + Sync since GreenNode is thread-safe
unsafe impl<T> Send for Parse<T> {}
unsafe impl<T> Sync for Parse<T> {}

impl<T> Parse<T> {
    /// Create a new Parse result from a GreenNode and errors
    pub fn new(green: GreenNode, errors: Vec<String>) -> Self {
        Parse {
            green,
            errors,
            _ty: std::marker::PhantomData,
        }
    }

    /// Get the green node (thread-safe representation)
    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    /// Get the syntax errors
    pub fn errors(&self) -> &[String] {
        &self.errors
    }

    /// Check if there are any errors
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// Convert to a Result, returning the tree if there are no errors
    pub fn to_result(self) -> Result<T, ParseError>
    where
        T: AstNode<Language = Lang>,
    {
        if self.errors.is_empty() {
            let node = SyntaxNode::new_root(self.green);
            Ok(T::cast(node).expect("root node has wrong type"))
        } else {
            Err(ParseError(self.errors))
        }
    }

    /// Convert to a Result, returning a mutable tree if there are no errors
    pub fn to_mut_result(self) -> Result<T, ParseError>
    where
        T: AstNode<Language = Lang>,
    {
        if self.errors.is_empty() {
            let node = SyntaxNode::new_root_mut(self.green);
            Ok(T::cast(node).expect("root node has wrong type"))
        } else {
            Err(ParseError(self.errors))
        }
    }

    /// Get the parsed syntax tree, panicking if there are errors
    pub fn tree(&self) -> T
    where
        T: AstNode<Language = Lang>,
    {
        assert!(
            self.errors.is_empty(),
            "tried to get tree with errors: {:?}",
            self.errors
        );
        let node = SyntaxNode::new_root(self.green.clone());
        T::cast(node).expect("root node has wrong type")
    }

    /// Get the syntax node
    pub fn syntax_node(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    /// Get a mutable parsed syntax tree, panicking if there are errors
    pub fn tree_mut(&self) -> T
    where
        T: AstNode<Language = Lang>,
    {
        assert!(
            self.errors.is_empty(),
            "tried to get tree with errors: {:?}",
            self.errors
        );
        let node = SyntaxNode::new_root_mut(self.green.clone());
        T::cast(node).expect("root node has wrong type")
    }
}

fn parse(text: &str) -> Parse<ChangeLog> {
    struct Parser {
        /// input tokens, including whitespace,
        /// in *reverse* order.
        tokens: Vec<(SyntaxKind, String)>,
        /// the in-progress tree.
        builder: GreenNodeBuilder<'static>,
        /// the list of syntax errors we've accumulated
        /// so far.
        errors: Vec<String>,
    }

    impl Parser {
        fn error(&mut self, msg: String) {
            self.builder.start_node(ERROR.into());
            if self.current().is_some() {
                self.bump();
            }
            self.errors.push(msg);
            self.builder.finish_node();
        }

        fn parse_entry_header(&mut self) {
            self.builder.start_node(ENTRY_HEADER.into());
            self.expect(IDENTIFIER);

            self.skip_ws();

            if self.current() == Some(NEWLINE) {
                self.bump();
                self.builder.finish_node();
                return;
            }

            self.expect(VERSION);

            self.skip_ws();

            self.builder.start_node(DISTRIBUTIONS.into());
            loop {
                match self.current() {
                    Some(IDENTIFIER) => self.bump(),
                    Some(NEWLINE) => {
                        self.bump();
                        self.builder.finish_node();
                        self.builder.finish_node();
                        return;
                    }
                    Some(SEMICOLON) => {
                        break;
                    }
                    _ => {
                        self.error("expected distribution or semicolon".to_string());
                        break;
                    }
                }
                self.skip_ws();
            }
            self.builder.finish_node();

            self.skip_ws();

            self.builder.start_node(METADATA.into());
            if self.current() == Some(SEMICOLON) {
                self.bump();
                loop {
                    self.skip_ws();

                    if self.current() == Some(NEWLINE) {
                        break;
                    }

                    self.builder.start_node(METADATA_ENTRY.into());
                    if self.current() == Some(IDENTIFIER) {
                        self.builder.start_node(METADATA_KEY.into());
                        self.bump();
                        self.builder.finish_node();
                    } else {
                        self.error("expected metadata key".to_string());
                        self.builder.finish_node();
                        break;
                    }

                    if self.current() == Some(EQUALS) {
                        self.bump();
                    } else {
                        self.error("expected equals".to_string());
                        self.builder.finish_node();
                        break;
                    }

                    if self.current() == Some(IDENTIFIER) {
                        self.builder.start_node(METADATA_VALUE.into());
                        self.bump();
                        self.builder.finish_node();
                    } else {
                        self.error("expected metadata value".to_string());
                        self.builder.finish_node();
                        break;
                    }
                    self.builder.finish_node();
                }
            } else if self.current() == Some(NEWLINE) {
            } else {
                self.error("expected semicolon or newline".to_string());
            }
            self.builder.finish_node();

            self.expect(NEWLINE);
            self.builder.finish_node();
        }

        fn parse_entry(&mut self) {
            self.builder.start_node(ENTRY.into());
            self.parse_entry_header();
            loop {
                match self
                    .tokens
                    .last()
                    .map(|(kind, token)| (kind, token.as_str()))
                {
                    None => {
                        self.error("unexpected end of file".to_string());
                        break;
                    }
                    // empty line
                    Some((NEWLINE, _)) => {
                        self.builder.start_node(EMPTY_LINE.into());
                        self.bump();
                        self.builder.finish_node();
                    }
                    // details
                    Some((INDENT, "  ")) => {
                        self.parse_entry_detail();
                    }
                    // footer
                    Some((INDENT, " -- ")) => {
                        self.parse_entry_footer();
                        break;
                    }
                    _ => break,
                }
            }

            self.builder.finish_node();
        }

        pub fn parse_entry_detail(&mut self) {
            self.builder.start_node(ENTRY_BODY.into());
            self.expect(INDENT);

            match self.current() {
                Some(DETAIL) => {
                    self.bump();
                }
                Some(NEWLINE) => {}
                _ => {
                    self.error("expected detail".to_string());
                }
            }

            self.expect(NEWLINE);
            self.builder.finish_node();
        }

        pub fn parse_entry_footer(&mut self) {
            self.builder.start_node(ENTRY_FOOTER.into());

            if self.current() != Some(INDENT) {
                self.error("expected indent".to_string());
            } else {
                let dashes = &self.tokens.last().unwrap().1;
                if dashes != " -- " {
                    self.error("expected --".to_string());
                } else {
                    self.bump();
                }
            }

            self.builder.start_node(MAINTAINER.into());
            while self.current() == Some(TEXT)
                || (self.current() == Some(WHITESPACE) && self.next() != Some(EMAIL))
            {
                self.bump();
            }
            self.builder.finish_node();

            if self.current().is_some() && self.current() != Some(NEWLINE) {
                self.expect(WHITESPACE);
            }

            if self.current().is_some() && self.current() != Some(NEWLINE) {
                self.expect(EMAIL);
            }

            if self.tokens.last().map(|(k, t)| (*k, t.as_str())) == Some((WHITESPACE, "  ")) {
                self.bump();
            } else if self.current() == Some(WHITESPACE) {
                self.error("expected two spaces".to_string());
            } else if self.current() == Some(NEWLINE) {
                self.bump();
                self.builder.finish_node();
                return;
            } else {
                self.error(format!("expected whitespace, got {:?}", self.current()));
            }

            self.builder.start_node(TIMESTAMP.into());

            loop {
                if self.current() != Some(TEXT) && self.current() != Some(WHITESPACE) {
                    break;
                }
                self.bump();
            }
            self.builder.finish_node();

            self.expect(NEWLINE);
            self.builder.finish_node();
        }

        fn parse(mut self) -> Parse<ChangeLog> {
            self.builder.start_node(ROOT.into());
            loop {
                match self.current() {
                    None => break,
                    Some(NEWLINE) => {
                        self.builder.start_node(EMPTY_LINE.into());
                        self.bump();
                        self.builder.finish_node();
                    }
                    Some(COMMENT) => {
                        self.bump();
                    }
                    Some(IDENTIFIER) => {
                        self.parse_entry();
                    }
                    t => {
                        self.error(format!("unexpected token {:?}", t));
                        break;
                    }
                }
            }
            // Close the root node.
            self.builder.finish_node();

            // Turn the builder into a GreenNode
            Parse::new(self.builder.finish(), self.errors)
        }
        /// Advance one token, adding it to the current branch of the tree builder.
        fn bump(&mut self) {
            let (kind, text) = self.tokens.pop().unwrap();
            self.builder.token(kind.into(), text.as_str());
        }
        /// Peek at the first unprocessed token
        fn current(&self) -> Option<SyntaxKind> {
            self.tokens.last().map(|(kind, _)| *kind)
        }

        fn next(&self) -> Option<SyntaxKind> {
            self.tokens
                .get(self.tokens.len() - 2)
                .map(|(kind, _)| *kind)
        }

        fn expect(&mut self, expected: SyntaxKind) {
            if self.current() != Some(expected) {
                self.error(format!("expected {:?}, got {:?}", expected, self.current()));
            } else {
                self.bump();
            }
        }
        fn skip_ws(&mut self) {
            while self.current() == Some(WHITESPACE) {
                self.bump()
            }
        }
    }

    let mut tokens = lex(text);
    tokens.reverse();
    Parser {
        tokens,
        builder: GreenNodeBuilder::new(),
        errors: Vec::new(),
    }
    .parse()
}

// To work with the parse results we need a view into the
// green tree - the Syntax tree.
// It is also immutable, like a GreenNode,
// but it contains parent pointers, offsets, and
// has identity semantics.

type SyntaxNode = rowan::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = rowan::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        /// A node in the changelog syntax tree.
        pub struct $ast(SyntaxNode);

        impl AstNode for $ast {
            type Language = Lang;

            fn can_cast(kind: SyntaxKind) -> bool {
                kind == $kind
            }

            fn cast(syntax: SyntaxNode) -> Option<Self> {
                if Self::can_cast(syntax.kind()) {
                    Some(Self(syntax))
                } else {
                    None
                }
            }

            fn syntax(&self) -> &SyntaxNode {
                &self.0
            }
        }

        impl $ast {
            #[allow(dead_code)]
            fn replace_root(&mut self, new_root: SyntaxNode) {
                self.0 = Self::cast(new_root).unwrap().0;
            }
        }

        impl std::fmt::Display for $ast {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str(self.0.text().to_string().as_str())
            }
        }
    };
}

ast_node!(ChangeLog, ROOT);
ast_node!(Entry, ENTRY);
ast_node!(EntryHeader, ENTRY_HEADER);
ast_node!(EntryBody, ENTRY_BODY);
ast_node!(EntryFooter, ENTRY_FOOTER);
ast_node!(Maintainer, MAINTAINER);
ast_node!(Timestamp, TIMESTAMP);
ast_node!(MetadataEntry, METADATA_ENTRY);
ast_node!(MetadataKey, METADATA_KEY);
ast_node!(MetadataValue, METADATA_VALUE);

impl MetadataEntry {
    pub fn key(&self) -> Option<String> {
        self.0
            .children()
            .find_map(MetadataKey::cast)
            .map(|k| k.to_string())
    }

    pub fn value(&self) -> Option<String> {
        self.0
            .children()
            .find_map(MetadataValue::cast)
            .map(|k| k.to_string())
    }

    pub fn set_value(&mut self, value: &str) {
        let node = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == METADATA_VALUE);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(METADATA_VALUE.into());
        builder.token(IDENTIFIER.into(), value);
        builder.finish_node();
        let root = SyntaxNode::new_root_mut(builder.finish());

        let range = if let Some(node) = node {
            node.index()..node.index() + 1
        } else {
            let count = self.0.children().count();
            count..count
        };

        self.0.splice_children(range, vec![root.into()]);
    }
}

/// A builder for a changelog entry.
pub struct EntryBuilder {
    root: SyntaxNode,
    package: Option<String>,
    version: Option<Version>,
    distributions: Option<Vec<String>>,
    urgency: Option<Urgency>,
    maintainer: Option<(String, String)>,
    timestamp: Option<chrono::DateTime<FixedOffset>>,
    change_lines: Vec<String>,
}

impl EntryBuilder {
    /// Set the package name
    #[must_use]
    pub fn package(mut self, package: String) -> Self {
        self.package = Some(package);
        self
    }

    /// Set the package version
    #[must_use]
    pub fn version(mut self, version: Version) -> Self {
        self.version = Some(version);
        self
    }

    /// Set the distribution(s)
    #[must_use]
    pub fn distributions(mut self, distributions: Vec<String>) -> Self {
        self.distributions = Some(distributions);
        self
    }

    #[must_use]
    pub fn distribution(mut self, distribution: String) -> Self {
        self.distributions
            .get_or_insert_with(Vec::new)
            .push(distribution);
        self
    }

    #[must_use]
    pub fn urgency(mut self, urgency: Urgency) -> Self {
        self.urgency = Some(urgency);
        self
    }

    #[must_use]
    pub fn maintainer(mut self, maintainer: (String, String)) -> Self {
        self.maintainer = Some(maintainer);
        self
    }

    #[must_use]
    pub fn datetime(mut self, timestamp: chrono::DateTime<FixedOffset>) -> Self {
        self.timestamp = Some(timestamp);
        self
    }

    #[must_use]
    pub fn change_line(mut self, line: String) -> Self {
        self.change_lines.push(line);
        self
    }

    pub fn verify(&self) -> Result<(), String> {
        if self.package.is_none() {
            return Err("package is required".to_string());
        }
        if self.version.is_none() {
            return Err("version is required".to_string());
        }
        match self.distributions {
            None => {
                return Err("at least one distribution is required".to_string());
            }
            Some(ref distributions) => {
                if distributions.is_empty() {
                    return Err("at least one distribution is required".to_string());
                }
            }
        }
        if self.change_lines.is_empty() {
            return Err("at least one change line is required".to_string());
        }
        Ok(())
    }

    fn metadata(&self) -> impl Iterator<Item = (String, String)> {
        let mut ret = vec![];
        if let Some(urgency) = self.urgency.as_ref() {
            ret.push(("urgency".to_string(), urgency.to_string()));
        }
        ret.into_iter()
    }

    pub fn finish(self) -> Entry {
        if self.root.children().find_map(Entry::cast).is_some() {
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(EMPTY_LINE.into());
            builder.token(NEWLINE.into(), "\n");
            builder.finish_node();
            let syntax = SyntaxNode::new_root_mut(builder.finish());
            self.root.splice_children(0..0, vec![syntax.into()]);
        }

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ENTRY.into());
        builder.start_node(ENTRY_HEADER.into());
        if let Some(package) = self.package.as_ref() {
            builder.token(IDENTIFIER.into(), package.as_str());
        }
        if let Some(version) = self.version.as_ref() {
            builder.token(WHITESPACE.into(), " ");
            builder.token(VERSION.into(), format!("({})", version).as_str());
        }
        if let Some(distributions) = self.distributions.as_ref() {
            builder.token(WHITESPACE.into(), " ");
            builder.start_node(DISTRIBUTIONS.into());
            let mut it = distributions.iter().peekable();
            while it.peek().is_some() {
                builder.token(IDENTIFIER.into(), it.next().unwrap());
                if it.peek().is_some() {
                    builder.token(WHITESPACE.into(), " ");
                }
            }
            builder.finish_node(); // DISTRIBUTIONS
        }
        let mut metadata = self.metadata().peekable();
        if metadata.peek().is_some() {
            builder.token(SEMICOLON.into(), ";");
            builder.token(WHITESPACE.into(), " ");
            builder.start_node(METADATA.into());
            for (key, value) in metadata {
                builder.start_node(METADATA_ENTRY.into());
                builder.start_node(METADATA_KEY.into());
                builder.token(IDENTIFIER.into(), key.as_str());
                builder.finish_node(); // METADATA_KEY
                builder.token(EQUALS.into(), "=");
                builder.start_node(METADATA_VALUE.into());
                builder.token(METADATA_VALUE.into(), value.as_str());
                builder.finish_node(); // METADATA_VALUE
                builder.finish_node(); // METADATA_ENTRY
            }
            builder.finish_node(); // METADATA
        }
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node(); // ENTRY_HEADER

        builder.start_node(EMPTY_LINE.into());
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node(); // EMPTY_LINE

        for line in self.change_lines {
            builder.start_node(ENTRY_BODY.into());
            builder.token(INDENT.into(), "  ");
            builder.token(DETAIL.into(), line.as_str());
            builder.token(NEWLINE.into(), "\n");
            builder.finish_node(); // ENTRY_BODY
        }

        builder.start_node(EMPTY_LINE.into());
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node(); // EMPTY_LINE

        builder.start_node(ENTRY_FOOTER.into());
        builder.token(INDENT.into(), " -- ");
        if let Some(maintainer) = self.maintainer.as_ref() {
            builder.start_node(MAINTAINER.into());
            let mut it = maintainer.0.split(' ').peekable();
            while let Some(p) = it.next() {
                builder.token(TEXT.into(), p);
                if it.peek().is_some() {
                    builder.token(WHITESPACE.into(), " ");
                }
            }
            builder.finish_node(); // MAINTAINER
        }

        if let Some(maintainer) = self.maintainer.as_ref() {
            builder.token(WHITESPACE.into(), " ");
            builder.token(EMAIL.into(), format!("<{}>", maintainer.1).as_str());
        }

        if let Some(timestamp) = self.timestamp.as_ref() {
            builder.token(WHITESPACE.into(), "  ");

            builder.start_node(TIMESTAMP.into());
            let ts = timestamp.format("%a, %d %b %Y %H:%M:%S %z").to_string();
            let mut it = ts.split(' ').peekable();
            while let Some(p) = it.next() {
                builder.token(TEXT.into(), p);
                if it.peek().is_some() {
                    builder.token(WHITESPACE.into(), " ");
                }
            }
            builder.finish_node(); // TIMESTAMP
        }
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node(); // ENTRY_FOOTER

        builder.finish_node(); // ENTRY
        let syntax = SyntaxNode::new_root_mut(builder.finish());
        self.root.splice_children(0..0, vec![syntax.clone().into()]);
        Entry(syntax)
    }
}

impl IntoIterator for ChangeLog {
    type Item = Entry;
    type IntoIter = std::vec::IntoIter<Entry>;

    fn into_iter(self) -> Self::IntoIter {
        // TODO: This is inefficient
        self.iter().collect::<Vec<_>>().into_iter()
    }
}

fn replay(builder: &mut GreenNodeBuilder, node: SyntaxNode) {
    builder.start_node(node.kind().into());
    for child in node.children_with_tokens() {
        match child {
            SyntaxElement::Node(n) => replay(builder, n),
            SyntaxElement::Token(t) => {
                builder.token(t.kind().into(), t.text());
            }
        }
    }
    builder.finish_node();
}

impl FromIterator<Entry> for ChangeLog {
    fn from_iter<T: IntoIterator<Item = Entry>>(iter: T) -> Self {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ROOT.into());
        for entry in iter {
            replay(&mut builder, entry.0.clone());
        }
        builder.finish_node();
        ChangeLog(SyntaxNode::new_root_mut(builder.finish()))
    }
}

impl ChangeLog {
    /// Create a new, empty changelog.
    pub fn new() -> ChangeLog {
        let mut builder = GreenNodeBuilder::new();

        builder.start_node(ROOT.into());
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        ChangeLog(syntax)
    }

    /// Parse changelog text, returning a Parse result
    pub fn parse(text: &str) -> Parse<ChangeLog> {
        parse(text)
    }

    /// Returns an iterator over all entries in the changelog file.
    pub fn iter(&self) -> impl Iterator<Item = Entry> + '_ {
        self.0.children().filter_map(Entry::cast)
    }

    /// Returns an iterator over all entries in the changelog file.
    #[deprecated(since = "0.2.0", note = "use `iter` instead")]
    pub fn entries(&self) -> impl Iterator<Item = Entry> + '_ {
        self.iter()
    }

    /// Create a new, empty entry.
    pub fn new_empty_entry(&mut self) -> EntryBuilder {
        EntryBuilder {
            root: self.0.clone(),
            package: None,
            version: None,
            distributions: None,
            urgency: None,
            maintainer: None,
            timestamp: None,
            change_lines: vec![],
        }
    }

    fn first_valid_entry(&self) -> Option<Entry> {
        self.iter().find(|entry| {
            entry.package().is_some() && entry.header().is_some() && entry.footer().is_some()
        })
    }

    /// Return a builder for a new entry.
    pub fn new_entry(&mut self) -> EntryBuilder {
        let base_entry = self.first_valid_entry();
        let package = base_entry
            .as_ref()
            .and_then(|first_entry| first_entry.package());
        let mut version = base_entry
            .as_ref()
            .and_then(|first_entry| first_entry.version());
        if let Some(version) = version.as_mut() {
            version.increment_debian();
        }
        EntryBuilder {
            root: if self.0.is_mutable() {
                self.0.clone()
            } else {
                self.0.clone_for_update()
            },
            package,
            version,
            distributions: Some(vec![crate::UNRELEASED.into()]),
            urgency: Some(Urgency::default()),
            maintainer: crate::get_maintainer(),
            timestamp: Some(chrono::Utc::now().into()),
            change_lines: vec![],
        }
    }

    /// Add a change to the changelog.
    ///
    /// This will update the current changelog entry if it is considered
    /// unreleased. Otherwise, a new entry will be created.
    ///
    /// If there is an existing entry, the change will be added to the end of
    /// the entry. If the previous change was attributed to another author,
    /// a new section line ("[ Author Name ]") will be added as well.
    ///
    /// # Arguments
    /// * `change` - The change to add, e.g. &["* Fix a bug"]
    /// * `author` - The author of the change, e.g. ("John Doe", "john@example")
    pub fn auto_add_change(
        &mut self,
        change: &[&str],
        author: (String, String),
        datetime: Option<DateTime<FixedOffset>>,
        urgency: Option<Urgency>,
    ) -> Entry {
        match self.first_valid_entry() {
            Some(entry) if entry.is_unreleased() != Some(false) => {
                // Add to existing entry
                entry.add_change_for_author(change, author);
                // TODO: set timestamp to std::cmp::max(entry.timestamp(), datetime)
                // TODO: set urgency to std::cmp::max(entry.urgency(), urgency)
                entry
            }
            Some(_entry) => {
                // Create new entry
                let mut builder = self.new_entry();
                builder = builder.maintainer(author);
                if let Some(datetime) = datetime {
                    builder = builder.datetime(datetime);
                }
                if let Some(urgency) = urgency {
                    builder = builder.urgency(urgency);
                }
                for change in change {
                    builder = builder.change_line(change.to_string());
                }
                builder.finish()
            }
            None => {
                panic!("No existing entries found in changelog");
            }
        }
    }

    /// Pop the first entry from the changelog.
    pub fn pop_first(&mut self) -> Option<Entry> {
        let mut it = self.iter();
        if let Some(entry) = it.next() {
            // Drop trailing newlines
            while let Some(sibling) = entry.0.next_sibling() {
                if sibling.kind() == EMPTY_LINE {
                    sibling.detach();
                } else {
                    break;
                }
            }
            entry.0.detach();
            Some(entry)
        } else {
            None
        }
    }

    /// Read a changelog file from a path
    pub fn read_path(path: impl AsRef<std::path::Path>) -> Result<ChangeLog, Error> {
        let mut file = std::fs::File::open(path)?;
        Self::read(&mut file)
    }

    /// Read a changelog file from a reader
    pub fn read<R: std::io::Read>(mut r: R) -> Result<ChangeLog, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;
        Ok(buf.parse()?)
    }

    /// Read a changelog file from a reader, allowing for syntax errors
    pub fn read_relaxed<R: std::io::Read>(mut r: R) -> Result<ChangeLog, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;

        let parsed = parse(&buf);
        // For relaxed parsing, we ignore errors and return the tree anyway
        let node = SyntaxNode::new_root_mut(parsed.green().clone());
        Ok(ChangeLog::cast(node).expect("root node has wrong type"))
    }

    /// Write the changelog to a writer
    pub fn write<W: std::io::Write>(&self, mut w: W) -> Result<(), Error> {
        let buf = self.to_string();
        w.write_all(buf.as_bytes())?;
        Ok(())
    }

    /// Write the changelog to a path
    pub fn write_to_path(&self, p: &std::path::Path) -> Result<(), Error> {
        let f = std::fs::File::create(p)?;
        self.write(f)?;
        Ok(())
    }
}

impl Default for ChangeLog {
    fn default() -> Self {
        Self::new()
    }
}

impl FromStr for ChangeLog {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ChangeLog::parse(s).to_mut_result()
    }
}

impl FromStr for Entry {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let cl: ChangeLog = s.parse()?;
        let mut entries = cl.iter();
        let entry = entries
            .next()
            .ok_or_else(|| ParseError(vec!["no entries found".to_string()]))?;
        if entries.next().is_some() {
            return Err(ParseError(vec!["multiple entries found".to_string()]));
        }
        Ok(entry)
    }
}

impl EntryHeader {
    /// Returns the version of the entry.
    pub fn version(&self) -> Option<Version> {
        self.0.children_with_tokens().find_map(|it| {
            if let Some(token) = it.as_token() {
                if token.kind() == VERSION {
                    let text = token.text()[1..token.text().len() - 1].to_string();
                    return Some(text.parse().unwrap());
                }
            }
            None
        })
    }

    /// Returns the package name of the entry.
    pub fn package(&self) -> Option<String> {
        self.0.children_with_tokens().find_map(|it| {
            if let Some(token) = it.as_token() {
                if token.kind() == IDENTIFIER {
                    return Some(token.text().to_string());
                }
            }
            None
        })
    }

    /// Returns the distributions of the entry.
    pub fn distributions(&self) -> Option<Vec<String>> {
        let node = self.0.children().find(|it| it.kind() == DISTRIBUTIONS);

        node.map(|node| {
            node.children_with_tokens()
                .filter_map(|it| {
                    if let Some(token) = it.as_token() {
                        if token.kind() == IDENTIFIER {
                            return Some(token.text().to_string());
                        }
                    }
                    None
                })
                .collect::<Vec<_>>()
        })
    }

    /// Set distributions for the entry.
    pub fn set_distributions(&mut self, _distributions: Vec<String>) {
        let node = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == DISTRIBUTIONS);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(DISTRIBUTIONS.into());
        for (i, distribution) in _distributions.iter().enumerate() {
            if i > 0 {
                builder.token(WHITESPACE.into(), " ");
            }
            builder.token(IDENTIFIER.into(), distribution);
        }
        builder.finish_node();

        let (range, green) = if let Some(node) = node {
            (
                node.index()..node.index() + 1,
                vec![builder.finish().into()],
            )
        } else if let Some(version) = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == VERSION)
        {
            (
                version.index()..version.index() + 1,
                vec![
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                    builder.finish().into(),
                ],
            )
        } else if let Some(metadata) = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == METADATA)
        {
            (
                metadata.index() - 1..metadata.index() - 1,
                vec![
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                    builder.finish().into(),
                ],
            )
        } else {
            (
                self.0.children().count()..self.0.children().count(),
                vec![
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                    builder.finish().into(),
                ],
            )
        };

        let new_root = SyntaxNode::new_root_mut(self.0.green().splice_children(range, green));
        self.replace_root(new_root);
    }

    /// Set the version for the entry.
    pub fn set_version(&mut self, version: &Version) {
        // Find the version token
        let node = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == VERSION);
        let (range, green) = if let Some(token) = node {
            (
                token.index()..token.index() + 1,
                vec![GreenToken::new(VERSION.into(), &format!("({})", version)).into()],
            )
        } else {
            let index = self
                .0
                .children_with_tokens()
                .position(|it| it.kind() == IDENTIFIER)
                .unwrap_or(0);
            (
                index + 1..index + 1,
                vec![
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                    GreenToken::new(VERSION.into(), &format!("({})", version)).into(),
                ],
            )
        };
        let new_root = SyntaxNode::new_root_mut(self.0.green().splice_children(range, green));

        self.replace_root(new_root);
    }

    /// Set the package name for the entry.
    pub fn set_package(&mut self, package: String) {
        let node = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == IDENTIFIER);

        let new_root = if let Some(token) = node {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                token.index()..token.index() + 1,
                vec![GreenToken::new(IDENTIFIER.into(), &package).into()],
            ))
        } else {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                0..0,
                vec![
                    GreenToken::new(IDENTIFIER.into(), &package).into(),
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                ],
            ))
        };

        self.replace_root(new_root);
    }

    /// Set extra metadata for the entry.
    pub fn set_metadata(&mut self, key: &str, value: &str) {
        // Find the appropriate metadata node
        if let Some(mut node) = self
            .metadata_nodes()
            .find(|it| it.key().map(|k| k == key).unwrap_or(false))
        {
            node.set_value(value);
        } else if let Some(metadata) = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == METADATA)
        {
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(METADATA_ENTRY.into());
            builder.start_node(METADATA_KEY.into());
            builder.token(IDENTIFIER.into(), key);
            builder.finish_node();
            builder.token(EQUALS.into(), "=");
            builder.start_node(METADATA_VALUE.into());
            builder.token(IDENTIFIER.into(), value);
            builder.finish_node();
            builder.finish_node();

            let metadata = metadata.as_node().unwrap();

            let count = metadata.children_with_tokens().count();
            self.0.splice_children(
                metadata.index()..metadata.index() + 1,
                vec![SyntaxNode::new_root_mut(metadata.green().splice_children(
                    count..count,
                    vec![
                        GreenToken::new(WHITESPACE.into(), " ").into(),
                        builder.finish().into(),
                    ],
                ))
                .into()],
            );
        } else {
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(METADATA.into());
            builder.token(SEMICOLON.into(), ";");
            builder.token(WHITESPACE.into(), " ");
            builder.start_node(METADATA_ENTRY.into());
            builder.start_node(METADATA_KEY.into());
            builder.token(IDENTIFIER.into(), key);
            builder.finish_node();
            builder.token(EQUALS.into(), "=");
            builder.start_node(METADATA_VALUE.into());
            builder.token(IDENTIFIER.into(), value);
            builder.finish_node();
            builder.finish_node();

            let new_root = SyntaxNode::new_root_mut(builder.finish());

            // Add either just after DISTRIBUTIONS
            if let Some(distributions) = self
                .0
                .children_with_tokens()
                .find(|it| it.kind() == DISTRIBUTIONS)
            {
                self.0.splice_children(
                    distributions.index() + 1..distributions.index() + 1,
                    vec![new_root.into()],
                );
            } else if let Some(nl) = self
                .0
                .children_with_tokens()
                .find(|it| it.kind() == NEWLINE)
            {
                // Just before the newline
                self.0
                    .splice_children(nl.index()..nl.index(), vec![new_root.into()]);
            } else {
                let count = self.0.children_with_tokens().count();
                self.0.splice_children(count..count, vec![new_root.into()]);
            }
        }
    }

    fn metadata_nodes(&self) -> impl Iterator<Item = MetadataEntry> + '_ {
        let node = self.0.children().find(|it| it.kind() == METADATA);

        node.into_iter().flat_map(|node| {
            node.children_with_tokens()
                .filter_map(|it| MetadataEntry::cast(it.into_node()?))
        })
    }

    pub fn metadata(&self) -> impl Iterator<Item = (String, String)> + '_ {
        self.metadata_nodes().filter_map(|entry| {
            if let (Some(key), Some(value)) = (entry.key(), entry.value()) {
                Some((key, value))
            } else {
                None
            }
        })
    }

    /// Returns the urgency of the entry.3
    pub fn urgency(&self) -> Option<Urgency> {
        for (key, value) in self.metadata() {
            if key.as_str() == "urgency" {
                return Some(value.parse().unwrap());
            }
        }
        None
    }
}

impl EntryFooter {
    pub fn email(&self) -> Option<String> {
        self.0.children_with_tokens().find_map(|it| {
            if let Some(token) = it.as_token() {
                let text = token.text();
                if token.kind() == EMAIL {
                    return Some(text[1..text.len() - 1].to_string());
                }
            }
            None
        })
    }

    pub fn maintainer(&self) -> Option<String> {
        self.0
            .children()
            .find_map(Maintainer::cast)
            .map(|m| m.text())
            .filter(|s| !s.is_empty())
    }

    /// Set the maintainer for the entry.
    pub fn set_maintainer(&mut self, maintainer: String) {
        let node = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == MAINTAINER);
        let new_root = if let Some(node) = node {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index()..node.index() + 1,
                vec![GreenToken::new(MAINTAINER.into(), &maintainer).into()],
            ))
        } else if let Some(node) = self.0.children_with_tokens().find(|it| it.kind() == INDENT) {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index() + 1..node.index() + 1,
                vec![GreenToken::new(MAINTAINER.into(), &maintainer).into()],
            ))
        } else {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                0..0,
                vec![
                    GreenToken::new(INDENT.into(), " -- ").into(),
                    GreenToken::new(MAINTAINER.into(), &maintainer).into(),
                ],
            ))
        };

        self.replace_root(new_root);
    }

    /// Set email for the entry.
    pub fn set_email(&mut self, _email: String) {
        let node = self.0.children_with_tokens().find(|it| it.kind() == EMAIL);
        let new_root = if let Some(node) = node {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index()..node.index() + 1,
                vec![GreenToken::new(EMAIL.into(), &format!("<{}>", _email)).into()],
            ))
        } else if let Some(node) = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == MAINTAINER)
        {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index() + 1..node.index() + 1,
                vec![GreenToken::new(EMAIL.into(), &format!("<{}>", _email)).into()],
            ))
        } else if let Some(node) = self.0.children_with_tokens().find(|it| it.kind() == INDENT) {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index() + 1..node.index() + 1,
                vec![
                    GreenToken::new(MAINTAINER.into(), "").into(),
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                    GreenToken::new(EMAIL.into(), &format!("<{}>", _email)).into(),
                ],
            ))
        } else {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                0..0,
                vec![
                    GreenToken::new(INDENT.into(), " -- ").into(),
                    GreenToken::new(MAINTAINER.into(), "").into(),
                    GreenToken::new(WHITESPACE.into(), " ").into(),
                    GreenToken::new(EMAIL.into(), &format!("<{}>", _email)).into(),
                ],
            ))
        };

        self.replace_root(new_root);
    }

    pub fn timestamp(&self) -> Option<String> {
        self.0
            .children()
            .find_map(Timestamp::cast)
            .map(|m| m.text())
    }

    /// Set timestamp for the entry.
    pub fn set_timestamp(&mut self, timestamp: String) {
        let node = self
            .0
            .children_with_tokens()
            .find(|it| it.kind() == TIMESTAMP);
        let new_root = if let Some(node) = node {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index()..node.index() + 1,
                vec![GreenToken::new(TIMESTAMP.into(), &timestamp).into()],
            ))
        } else if let Some(node) = self.0.children_with_tokens().find(|it| it.kind() == INDENT) {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index() + 1..node.index() + 1,
                vec![GreenToken::new(TIMESTAMP.into(), &timestamp).into()],
            ))
        } else if let Some(node) = self.0.children_with_tokens().find(|it| it.kind() == EMAIL) {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                node.index() + 1..node.index() + 1,
                vec![GreenToken::new(TIMESTAMP.into(), &timestamp).into()],
            ))
        } else {
            SyntaxNode::new_root_mut(self.0.green().splice_children(
                0..0,
                vec![
                    GreenToken::new(INDENT.into(), " -- ").into(),
                    GreenToken::new(TIMESTAMP.into(), &timestamp).into(),
                ],
            ))
        };

        self.replace_root(new_root);
    }
}

impl EntryBody {
    fn text(&self) -> String {
        self.0
            .children_with_tokens()
            .filter_map(|it| {
                if let Some(token) = it.as_token() {
                    if token.kind() == DETAIL {
                        return Some(token.text().to_string());
                    }
                }
                None
            })
            .collect::<Vec<_>>()
            .concat()
    }
}

impl Timestamp {
    fn text(&self) -> String {
        self.0.text().to_string()
    }
}

impl Maintainer {
    fn text(&self) -> String {
        self.0.text().to_string()
    }
}

impl Entry {
    fn header(&self) -> Option<EntryHeader> {
        self.0.children().find_map(EntryHeader::cast)
    }

    fn footer(&self) -> Option<EntryFooter> {
        self.0.children().find_map(EntryFooter::cast)
    }

    /// Return the package name of the entry.
    pub fn package(&self) -> Option<String> {
        self.header().and_then(|h| h.package())
    }

    /// Set the package name of the entry.
    pub fn set_package(&mut self, package: String) {
        if let Some(mut header) = self.header() {
            let header_index = header.0.index();
            header.set_package(package);
            self.0
                .splice_children(header_index..header_index + 1, vec![header.0.into()]);
        } else {
            self.create_header().set_package(package);
        }
    }

    /// Return the version of the entry.
    pub fn version(&self) -> Option<Version> {
        self.header().and_then(|h| h.version())
    }

    /// Set the version of the entry.
    pub fn set_version(&mut self, version: &Version) {
        if let Some(mut header) = self.header() {
            let header_index = header.0.index();
            header.set_version(version);
            self.0
                .splice_children(header_index..header_index + 1, vec![header.0.into()]);
        } else {
            self.create_header().set_version(version);
        }
    }

    /// Return the distributions of the entry.
    pub fn distributions(&self) -> Option<Vec<String>> {
        self.header().and_then(|h| h.distributions())
    }

    /// Set the distributions for the entry
    pub fn set_distributions(&mut self, distributions: Vec<String>) {
        if let Some(mut header) = self.header() {
            let header_index = header.0.index();
            header.set_distributions(distributions);
            self.0
                .splice_children(header_index..header_index + 1, vec![header.0.into()]);
        } else {
            self.create_header().set_distributions(distributions);
        }
    }

    /// Returns the email address of the maintainer.
    pub fn email(&self) -> Option<String> {
        self.footer().and_then(|f| f.email())
    }

    /// Returns the name of the maintainer.
    pub fn maintainer(&self) -> Option<String> {
        self.footer().and_then(|f| f.maintainer())
    }

    /// Set the maintainer of the entry.
    pub fn set_maintainer(&mut self, maintainer: (String, String)) {
        if let Some(mut footer) = self.footer() {
            let footer_index = footer.0.index();
            footer.set_maintainer(maintainer.0);
            footer.set_email(maintainer.1);
            self.0
                .splice_children(footer_index..footer_index + 1, vec![footer.0.into()]);
        } else {
            let mut footer = self.create_footer();
            footer.set_maintainer(maintainer.0);
            footer.set_email(maintainer.1);
        }
    }

    /// Returns the timestamp of the entry, as the raw string.
    pub fn timestamp(&self) -> Option<String> {
        self.footer().and_then(|f| f.timestamp())
    }

    /// Set the timestamp of the entry.
    pub fn set_timestamp(&mut self, timestamp: String) {
        if let Some(mut footer) = self.footer() {
            let footer_index = footer.0.index();
            footer.set_timestamp(timestamp);
            self.0
                .splice_children(footer_index..footer_index + 1, vec![footer.0.into()]);
        } else {
            self.create_footer().set_timestamp(timestamp);
        }
    }

    /// Set the datetime of the entry.
    pub fn set_datetime(&mut self, datetime: DateTime<FixedOffset>) {
        self.set_timestamp(format!("{}", datetime.format("%a, %d %b %Y %H:%M:%S %z")));
    }

    /// Returns the datetime of the entry.
    pub fn datetime(&self) -> Option<DateTime<FixedOffset>> {
        self.timestamp().and_then(|ts| parse_time_string(&ts).ok())
    }

    /// Returns the urgency of the entry.
    pub fn urgency(&self) -> Option<Urgency> {
        self.header().and_then(|h| h.urgency())
    }

    fn create_header(&self) -> EntryHeader {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ENTRY_HEADER.into());
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();
        let syntax = SyntaxNode::new_root_mut(builder.finish());
        self.0.splice_children(0..0, vec![syntax.into()]);
        EntryHeader(self.0.children().next().unwrap().clone_for_update())
    }

    fn create_footer(&self) -> EntryFooter {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ENTRY_FOOTER.into());
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();
        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let count = self.0.children().count();
        self.0.splice_children(count..count, vec![syntax.into()]);
        EntryFooter(self.0.children().last().unwrap().clone_for_update())
    }

    /// Set the urgency of the entry.
    pub fn set_urgency(&mut self, urgency: Urgency) {
        self.set_metadata("urgency", urgency.to_string().as_str());
    }

    /// Set a metadata key-value pair for the entry.
    pub fn set_metadata(&mut self, key: &str, value: &str) {
        if let Some(mut header) = self.header() {
            let header_index = header.0.index();
            header.set_metadata(key, value);
            self.0
                .splice_children(header_index..header_index + 1, vec![header.0.into()]);
        } else {
            self.create_header().set_metadata(key, value);
        }
    }

    /// Add a change for the specified author
    ///
    /// If the author is not the same as the current maintainer, a new
    /// section will be created for the author in the entry (e.g. "[ John Doe ]").
    pub fn add_change_for_author(&self, change: &[&str], author: (String, String)) {
        let changes_lines = self.change_lines().collect::<Vec<_>>();
        let by_author = crate::changes::changes_by_author(changes_lines.iter().map(|s| s.as_str()))
            .collect::<Vec<_>>();

        // There are no per author sections yet, so attribute current changes to changelog entry author
        if by_author.iter().all(|(a, _, _)| a.is_none()) {
            if let Some(maintainer_name) = self.maintainer() {
                if author.0 != maintainer_name {
                    self.prepend_change_line(
                        crate::changes::format_section_title(maintainer_name.as_str()).as_str(),
                    );
                    if !self.change_lines().last().unwrap().is_empty() {
                        self.append_change_line("");
                    }
                    self.append_change_line(
                        crate::changes::format_section_title(author.0.as_str()).as_str(),
                    );
                }
            }
        } else if let Some(last_section) = by_author.last().as_ref() {
            if last_section.0 != Some(author.0.as_str()) {
                self.append_change_line("");
                self.append_change_line(
                    crate::changes::format_section_title(author.0.as_str()).as_str(),
                );
            }
        }

        if let Some(last) = self.change_lines().last() {
            if last.trim().is_empty() {
                self.pop_change_line();
            }
        }

        for line in crate::textwrap::rewrap_changes(change.iter().copied()) {
            self.append_change_line(line.as_ref());
        }
    }

    /// Prepend a change line to the entry
    pub fn prepend_change_line(&self, line: &str) {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ENTRY_BODY.into());
        if !line.is_empty() {
            builder.token(INDENT.into(), "  ");
            builder.token(DETAIL.into(), line);
        }
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        // Insert just after the header
        let mut it = self.0.children();
        let header = it.find(|n| n.kind() == ENTRY_HEADER);

        let previous_line = it.find(|n| n.kind() == EMPTY_LINE).or(header);

        let index = previous_line.map_or(0, |l| l.index() + 1);

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        self.0.splice_children(index..index, vec![syntax.into()]);
    }

    /// Pop the last change line from the entry
    pub fn pop_change_line(&self) -> Option<String> {
        // Find the last child of type ENTRY_BODY
        let last_child = self.0.children().filter(|n| n.kind() == ENTRY_BODY).last();

        if let Some(last_child) = last_child {
            let text = last_child.children_with_tokens().find_map(|it| {
                if let Some(token) = it.as_token() {
                    if token.kind() == DETAIL {
                        return Some(token.text().to_string());
                    }
                }
                None
            });
            self.0
                .splice_children(last_child.index()..last_child.index() + 1, vec![]);
            text
        } else {
            None
        }
    }

    /// Append a line to the changelog entry
    pub fn append_change_line(&self, line: &str) {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ENTRY_BODY.into());
        if !line.is_empty() {
            builder.token(INDENT.into(), "  ");
            builder.token(DETAIL.into(), line);
        }
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        // Find the last child of type ENTRY_BODY
        let last_child = self
            .0
            .children()
            .filter(|n| n.kind() == ENTRY_BODY)
            .last()
            .unwrap_or_else(|| self.0.children().next().unwrap());

        let syntax = SyntaxNode::new_root_mut(builder.finish()).into();
        self.0
            .splice_children(last_child.index() + 1..last_child.index() + 1, vec![syntax]);
    }

    /// Returns the changes of the entry.
    pub fn change_lines(&self) -> impl Iterator<Item = String> + '_ {
        let mut lines = self
            .0
            .children()
            .filter_map(|n| {
                if let Some(ref change) = EntryBody::cast(n.clone()) {
                    Some(change.text())
                } else if n.kind() == EMPTY_LINE {
                    Some("".to_string())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        while let Some(last) = lines.last() {
            if last.is_empty() {
                lines.pop();
            } else {
                break;
            }
        }

        lines.into_iter().skip_while(|it| it.is_empty())
    }

    /// Ensure that the first line of the entry is the specified line
    ///
    /// If the first line is not the specified line, it will be prepended to the entry.
    pub fn ensure_first_line(&self, line: &str) {
        let first_line = self.change_lines().next().map(|it| it.trim().to_string());

        if first_line != Some(line.to_string()) {
            self.prepend_change_line(line);
        }
    }

    /// Return whether the entry is marked as being unreleased
    pub fn is_unreleased(&self) -> Option<bool> {
        let distro_is_unreleased = self.distributions().as_ref().map(|ds| {
            let ds = ds.iter().map(|d| d.as_str()).collect::<Vec<&str>>();
            crate::distributions_is_unreleased(ds.as_slice())
        });

        let footer_is_unreleased = if self.maintainer().is_none() && self.email().is_none() {
            Some(true)
        } else {
            None
        };

        match (distro_is_unreleased, footer_is_unreleased) {
            (Some(true), _) => Some(true),
            (_, Some(true)) => Some(true),
            (Some(false), _) => Some(false),
            (_, Some(false)) => Some(false),
            _ => None,
        }
    }
}

const CHANGELOG_TIME_FORMAT: &str = "%a, %d %b %Y %H:%M:%S %z";

fn parse_time_string(time_str: &str) -> Result<DateTime<FixedOffset>, chrono::ParseError> {
    DateTime::parse_from_str(time_str, CHANGELOG_TIME_FORMAT)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple() {
        const CHANGELOG: &str = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500

breezy (3.3.3-2) unstable; urgency=medium

  * Drop unnecessary dependency on python3-six. Closes: #1039011
  * Drop dependency on cython3-dbg. Closes: #1040544

 -- Jelmer Vernooĳ <jelmer@debian.org>  Sat, 24 Jun 2023 14:58:57 +0100

# Oh, and here is a comment
"#;
        let parsed = parse(CHANGELOG);
        assert_eq!(parsed.errors(), &Vec::<String>::new());
        let node = parsed.syntax_node();
        assert_eq!(
            format!("{:#?}", node),
            r###"ROOT@0..405
  ENTRY@0..140
    ENTRY_HEADER@0..39
      IDENTIFIER@0..6 "breezy"
      WHITESPACE@6..7 " "
      VERSION@7..16 "(3.3.4-1)"
      WHITESPACE@16..17 " "
      DISTRIBUTIONS@17..25
        IDENTIFIER@17..25 "unstable"
      METADATA@25..38
        SEMICOLON@25..26 ";"
        WHITESPACE@26..27 " "
        METADATA_ENTRY@27..38
          METADATA_KEY@27..34
            IDENTIFIER@27..34 "urgency"
          EQUALS@34..35 "="
          METADATA_VALUE@35..38
            IDENTIFIER@35..38 "low"
      NEWLINE@38..39 "\n"
    EMPTY_LINE@39..40
      NEWLINE@39..40 "\n"
    ENTRY_BODY@40..66
      INDENT@40..42 "  "
      DETAIL@42..65 "* New upstream release."
      NEWLINE@65..66 "\n"
    EMPTY_LINE@66..67
      NEWLINE@66..67 "\n"
    ENTRY_FOOTER@67..140
      INDENT@67..71 " -- "
      MAINTAINER@71..86
        TEXT@71..77 "Jelmer"
        WHITESPACE@77..78 " "
        TEXT@78..86 "Vernooĳ"
      WHITESPACE@86..87 " "
      EMAIL@87..106 "<jelmer@debian.org>"
      WHITESPACE@106..108 "  "
      TIMESTAMP@108..139
        TEXT@108..112 "Mon,"
        WHITESPACE@112..113 " "
        TEXT@113..115 "04"
        WHITESPACE@115..116 " "
        TEXT@116..119 "Sep"
        WHITESPACE@119..120 " "
        TEXT@120..124 "2023"
        WHITESPACE@124..125 " "
        TEXT@125..133 "18:13:45"
        WHITESPACE@133..134 " "
        TEXT@134..139 "-0500"
      NEWLINE@139..140 "\n"
  EMPTY_LINE@140..141
    NEWLINE@140..141 "\n"
  ENTRY@141..376
    ENTRY_HEADER@141..183
      IDENTIFIER@141..147 "breezy"
      WHITESPACE@147..148 " "
      VERSION@148..157 "(3.3.3-2)"
      WHITESPACE@157..158 " "
      DISTRIBUTIONS@158..166
        IDENTIFIER@158..166 "unstable"
      METADATA@166..182
        SEMICOLON@166..167 ";"
        WHITESPACE@167..168 " "
        METADATA_ENTRY@168..182
          METADATA_KEY@168..175
            IDENTIFIER@168..175 "urgency"
          EQUALS@175..176 "="
          METADATA_VALUE@176..182
            IDENTIFIER@176..182 "medium"
      NEWLINE@182..183 "\n"
    EMPTY_LINE@183..184
      NEWLINE@183..184 "\n"
    ENTRY_BODY@184..249
      INDENT@184..186 "  "
      DETAIL@186..248 "* Drop unnecessary de ..."
      NEWLINE@248..249 "\n"
    ENTRY_BODY@249..302
      INDENT@249..251 "  "
      DETAIL@251..301 "* Drop dependency on  ..."
      NEWLINE@301..302 "\n"
    EMPTY_LINE@302..303
      NEWLINE@302..303 "\n"
    ENTRY_FOOTER@303..376
      INDENT@303..307 " -- "
      MAINTAINER@307..322
        TEXT@307..313 "Jelmer"
        WHITESPACE@313..314 " "
        TEXT@314..322 "Vernooĳ"
      WHITESPACE@322..323 " "
      EMAIL@323..342 "<jelmer@debian.org>"
      WHITESPACE@342..344 "  "
      TIMESTAMP@344..375
        TEXT@344..348 "Sat,"
        WHITESPACE@348..349 " "
        TEXT@349..351 "24"
        WHITESPACE@351..352 " "
        TEXT@352..355 "Jun"
        WHITESPACE@355..356 " "
        TEXT@356..360 "2023"
        WHITESPACE@360..361 " "
        TEXT@361..369 "14:58:57"
        WHITESPACE@369..370 " "
        TEXT@370..375 "+0100"
      NEWLINE@375..376 "\n"
  EMPTY_LINE@376..377
    NEWLINE@376..377 "\n"
  COMMENT@377..405 "# Oh, and here is a c ..."
"###
        );

        let mut root = parsed.tree_mut();
        let entries: Vec<_> = root.iter().collect();
        assert_eq!(entries.len(), 2);
        let entry = &entries[0];
        assert_eq!(entry.package(), Some("breezy".into()));
        assert_eq!(entry.version(), Some("3.3.4-1".parse().unwrap()));
        assert_eq!(entry.distributions(), Some(vec!["unstable".into()]));
        assert_eq!(entry.urgency(), Some(Urgency::Low));
        assert_eq!(entry.maintainer(), Some("Jelmer Vernooĳ".into()));
        assert_eq!(entry.email(), Some("jelmer@debian.org".into()));
        assert_eq!(
            entry.timestamp(),
            Some("Mon, 04 Sep 2023 18:13:45 -0500".into())
        );
        assert_eq!(
            entry.datetime(),
            Some("2023-09-04T18:13:45-05:00".parse().unwrap())
        );
        let changes_lines: Vec<_> = entry.change_lines().collect();
        assert_eq!(changes_lines, vec!["* New upstream release.".to_string()]);

        assert_eq!(node.text(), CHANGELOG);

        let first = root.pop_first().unwrap();
        assert_eq!(first.version(), Some("3.3.4-1".parse().unwrap()));
        assert_eq!(
            root.to_string(),
            r#"breezy (3.3.3-2) unstable; urgency=medium

  * Drop unnecessary dependency on python3-six. Closes: #1039011
  * Drop dependency on cython3-dbg. Closes: #1040544

 -- Jelmer Vernooĳ <jelmer@debian.org>  Sat, 24 Jun 2023 14:58:57 +0100

# Oh, and here is a comment
"#
        );
    }

    #[test]
    fn test_from_io_read() {
        let changelog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#;

        let input = changelog.as_bytes();
        let input = Box::new(std::io::Cursor::new(input)) as Box<dyn std::io::Read>;
        let parsed = ChangeLog::read(input).unwrap();
        assert_eq!(parsed.to_string(), changelog);
    }

    #[test]
    fn test_new_entry() {
        let mut cl = ChangeLog::new();
        cl.new_entry()
            .package("breezy".into())
            .version("3.3.4-1".parse().unwrap())
            .distributions(vec!["unstable".into()])
            .urgency(Urgency::Low)
            .maintainer(("Jelmer Vernooĳ".into(), "jelmer@debian.org".into()))
            .change_line("* A change.".into())
            .datetime("2023-09-04T18:13:45-05:00".parse().unwrap())
            .finish();
        assert_eq!(
            r###"breezy (3.3.4-1) unstable; urgency=low

  * A change.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"###,
            cl.to_string()
        );

        assert!(!cl.iter().next().unwrap().is_unreleased().unwrap());
    }

    #[test]
    fn test_new_empty_default() {
        let mut cl = ChangeLog::new();
        cl.new_entry()
            .package("breezy".into())
            .version("3.3.4-1".parse().unwrap())
            .maintainer(("Jelmer Vernooĳ".into(), "jelmer@debian.org".into()))
            .change_line("* A change.".into())
            .datetime("2023-09-04T18:13:45-05:00".parse().unwrap())
            .finish();
        assert_eq!(
            r###"breezy (3.3.4-1) UNRELEASED; urgency=low

  * A change.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"###,
            cl.to_string()
        );
    }

    #[test]
    fn test_new_empty_entry() {
        let mut cl = ChangeLog::new();
        cl.new_empty_entry()
            .change_line("* A change.".into())
            .finish();
        assert_eq!(
            r###"

  * A change.

 -- 
"###,
            cl.to_string()
        );
        assert_eq!(cl.iter().next().unwrap().is_unreleased(), Some(true));
    }

    #[test]
    fn test_parse_invalid_line() {
        let text = r#"THIS IS NOT A PARSEABLE LINE
lintian-brush (0.35) UNRELEASED; urgency=medium

  * Support updating templated debian/control files that use cdbs
    template.

 -- Joe Example <joe@example.com>  Fri, 04 Oct 2019 02:36:13 +0000
"#;
        let cl = ChangeLog::read_relaxed(text.as_bytes()).unwrap();
        let entry = cl.iter().nth(1).unwrap();
        assert_eq!(entry.package(), Some("lintian-brush".into()));
        assert_eq!(entry.version(), Some("0.35".parse().unwrap()));
        assert_eq!(entry.urgency(), Some(Urgency::Medium));
        assert_eq!(entry.maintainer(), Some("Joe Example".into()));
        assert_eq!(entry.email(), Some("joe@example.com".into()));
        assert_eq!(entry.distributions(), Some(vec!["UNRELEASED".into()]));
        assert_eq!(
            entry.datetime(),
            Some("2019-10-04T02:36:13+00:00".parse().unwrap())
        );
    }

    #[cfg(test)]
    mod entry_manipulate_tests {
        use super::*;

        #[test]
        fn test_append_change_line() {
            let mut cl = ChangeLog::new();

            let entry = cl
                .new_empty_entry()
                .change_line("* A change.".into())
                .finish();

            entry.append_change_line("* Another change.");

            assert_eq!(
                r###"

  * A change.
  * Another change.

 -- 
"###,
                cl.to_string()
            );
        }

        #[test]
        fn test_prepend_change_line() {
            let mut cl = ChangeLog::new();

            let entry = cl
                .new_empty_entry()
                .change_line("* A change.".into())
                .finish();

            entry.prepend_change_line("* Another change.");

            assert_eq!(
                r###"

  * Another change.
  * A change.

 -- 
"###,
                cl.to_string()
            );

            assert_eq!(entry.maintainer(), None);
            assert_eq!(entry.email(), None);
            assert_eq!(entry.timestamp(), None);
            assert_eq!(entry.package(), None);
            assert_eq!(entry.version(), None);
        }
    }

    #[cfg(test)]
    mod auto_add_change_tests {
        #[test]
        fn test_unreleased_existing() {
            let text = r#"lintian-brush (0.35) unstable; urgency=medium

  * This line already existed.

  [ Jane Example ]
  * And this one has an existing author.

 -- 
"#;
            let mut cl = super::ChangeLog::read(text.as_bytes()).unwrap();

            let entry = cl.iter().next().unwrap();
            assert_eq!(entry.package(), Some("lintian-brush".into()));
            assert_eq!(entry.is_unreleased(), Some(true));

            let entry = cl.auto_add_change(
                &["* And this one is new."],
                ("Joe Example".to_string(), "joe@example.com".to_string()),
                None,
                None,
            );

            assert_eq!(cl.iter().count(), 1);

            assert_eq!(entry.package(), Some("lintian-brush".into()));
            assert_eq!(entry.is_unreleased(), Some(true));
            assert_eq!(
                entry.change_lines().collect::<Vec<_>>(),
                &[
                    "* This line already existed.",
                    "",
                    "[ Jane Example ]",
                    "* And this one has an existing author.",
                    "",
                    "[ Joe Example ]",
                    "* And this one is new.",
                ]
            );
        }
    }

    #[test]
    fn test_ensure_first_line() {
        let text = r#"lintian-brush (0.35) unstable; urgency=medium

  * This line already existed.

  [ Jane Example ]
  * And this one has an existing author.

 -- 
"#;
        let cl = ChangeLog::read(text.as_bytes()).unwrap();

        let entry = cl.iter().next().unwrap();
        assert_eq!(entry.package(), Some("lintian-brush".into()));

        entry.ensure_first_line("* QA upload.");
        entry.ensure_first_line("* QA upload.");

        assert_eq!(
            r#"lintian-brush (0.35) unstable; urgency=medium

  * QA upload.
  * This line already existed.

  [ Jane Example ]
  * And this one has an existing author.

 -- 
"#,
            cl.to_string()
        );
    }

    #[test]
    fn test_set_version() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_version(&"3.3.5-1".parse().unwrap());

        assert_eq!(
            r#"breezy (3.3.5-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_package() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_package("bzr".into());

        assert_eq!(
            r#"bzr (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_distributions() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_distributions(vec!["unstable".into(), "experimental".into()]);

        assert_eq!(
            r#"breezy (3.3.4-1) unstable experimental; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_distributions_no_existing() {
        let mut entry: Entry = r#"breezy (3.3.4-1); urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_distributions(vec!["unstable".into()]);

        assert!(entry.to_string().contains("unstable"));
    }

    #[test]
    fn test_set_maintainer() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_maintainer(("Joe Example".into(), "joe@example.com".into()));

        assert_eq!(
            r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Joe Example <joe@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_timestamp() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_timestamp("Mon, 04 Sep 2023 18:13:46 -0500".into());

        assert_eq!(
            r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:46 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_datetime() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <joe@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_datetime("2023-09-04T18:13:46-05:00".parse().unwrap());

        assert_eq!(
            r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <joe@example.com>  Mon, 04 Sep 2023 18:13:46 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_urgency() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_urgency(Urgency::Medium);

        assert_eq!(
            r#"breezy (3.3.4-1) unstable; urgency=medium

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_metadata() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_metadata("foo", "bar");

        assert_eq!(
            r#"breezy (3.3.4-1) unstable; urgency=low foo=bar

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_metadata_replace_existing() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low foo=old

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_metadata("foo", "new");

        assert_eq!(
            r#"breezy (3.3.4-1) unstable; urgency=low foo=new

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_set_metadata_after_distributions() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable experimental; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_metadata("foo", "bar");

        assert_eq!(
            r#"breezy (3.3.4-1) unstable experimental; urgency=low foo=bar

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#,
            entry.to_string()
        );
    }

    #[test]
    fn test_add_change_for_author() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

  [ Jelmer Vernooĳ ]
  * A change by the maintainer.

 -- Joe Example <joe@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.add_change_for_author(
            &["A change by the maintainer."],
            ("Jelmer Vernooĳ".into(), "jelmer@debian.org".into()),
        );
    }

    #[test]
    fn test_changelog_from_entry_iter() {
        let text = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@jelmer.uk>  Mon, 04 Sep 2023 18:13:45 -0500
"#;

        let entry: Entry = text.parse().unwrap();

        let cl = std::iter::once(entry).collect::<ChangeLog>();

        assert_eq!(cl.to_string(), text);
    }

    #[test]
    fn test_pop_change_line() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.
  * Fixed bug #123.
  * Added new feature.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        // Test popping existing lines
        assert_eq!(
            entry.pop_change_line(),
            Some("* Added new feature.".to_string())
        );
        assert_eq!(
            entry.pop_change_line(),
            Some("* Fixed bug #123.".to_string())
        );
        assert_eq!(
            entry.pop_change_line(),
            Some("* New upstream release.".to_string())
        );

        // Test popping from empty entry
        assert_eq!(entry.pop_change_line(), None);
    }

    #[test]
    fn test_pop_change_line_empty_entry() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        assert_eq!(entry.pop_change_line(), None);
    }

    #[test]
    fn test_pop_change_line_empty_string() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * Something

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.pop_change_line();
        entry.append_change_line("");
        // Empty lines don't have DETAIL tokens, so pop_change_line returns None
        assert_eq!(entry.pop_change_line(), None);
    }

    #[test]
    fn test_append_change_line() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.append_change_line("* Fixed bug #456.");

        assert_eq!(
            entry.to_string(),
            r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.
  * Fixed bug #456.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        );
    }

    #[test]
    fn test_append_change_line_empty() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.append_change_line("");

        let lines: Vec<String> = entry.change_lines().collect();
        // Empty lines are not returned by change_lines()
        assert_eq!(lines.len(), 1);
        assert_eq!(lines[0], "* New upstream release.".to_string());
    }

    #[test]
    fn test_changelog_write_to_path() {
        use tempfile::NamedTempFile;

        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();

        changelog.write_to_path(&path).unwrap();

        let contents = std::fs::read_to_string(&path).unwrap();
        assert_eq!(contents, changelog.to_string());
    }

    #[test]
    fn test_changelog_into_iter() {
        let changelog: ChangeLog = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500

breezy (3.3.3-1) unstable; urgency=low

  * Previous release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 03 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        let entries: Vec<Entry> = changelog.into_iter().collect();
        assert_eq!(entries.len(), 2);
    }

    #[test]
    fn test_set_version_no_existing() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        entry.set_version(&"1.0.0".parse().unwrap());

        assert!(entry.to_string().contains("(1.0.0)"));
    }

    #[test]
    fn test_entry_footer_set_email_edge_cases() {
        let entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        // Test checking email through entry
        assert_eq!(entry.email(), Some("jelmer@debian.org".to_string()));
    }

    #[test]
    fn test_entry_footer_set_maintainer_edge_cases() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0500
"#
        .parse()
        .unwrap();

        // Test setting maintainer
        entry.set_maintainer(("New Maintainer".into(), "new@example.com".into()));

        assert!(entry
            .to_string()
            .contains("New Maintainer <new@example.com>"));
    }

    #[test]
    fn test_entry_footer_set_timestamp_edge_cases() {
        let mut entry: Entry = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  
"#
        .parse()
        .unwrap();

        // Test setting timestamp when it's missing
        entry.set_timestamp("Mon, 04 Sep 2023 18:13:45 -0500".into());

        assert!(entry
            .to_string()
            .contains("Mon, 04 Sep 2023 18:13:45 -0500"));
    }
}
