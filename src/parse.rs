use crate::lex::lex;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// Second, implementing the `Language` trait teaches rowan to convert between
/// these two SyntaxKind types, allowing for a nicer SyntaxNode API where
/// "kinds" are values from our `enum SyntaxKind`, instead of plain u16 values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Lang {}
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
use rowan::GreenNode;

/// You can construct GreenNodes by hand, but a builder
/// is helpful for top-down parsers: it maintains a stack
/// of currently in-progress nodes
use rowan::GreenNodeBuilder;

/// The parse results are stored as a "green tree".
/// We'll discuss working with the results later
struct Parse {
    green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<String>,
}

fn parse(text: &str) -> Parse {
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

            self.expect(VERSION);

            self.builder.start_node(DISTRIBUTIONS.into());
            loop {
                self.skip_ws();

                match self.current() {
                    Some(IDENTIFIER) => self.bump(),
                    Some(SEMICOLON) => {
                        break;
                    }
                    _ => {
                        self.error("expected distribution or semicolon".to_string());
                        break;
                    }
                }
            }
            self.builder.finish_node();

            if self.current() == Some(SEMICOLON) {
                self.bump();
                self.builder.start_node(METADATA.into());
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

            if self.current() == Some(NEWLINE) {
                self.bump();
            } else {
                self.error("expected newline".to_string());
            }
        }

        fn parse_entry(&mut self) {
            self.builder.start_node(ENTRY.into());
            self.parse_entry_header();
            loop {
                match self.current() {
                    None => {
                        self.error("unexpected end of file".to_string());
                        break;
                    }
                    // empty line
                    Some(NEWLINE) => {
                        self.bump();
                    }
                    Some(INDENT) if self.tokens.last().unwrap().1.len() == 2 => {
                        self.parse_entry_detail();
                    }
                    Some(INDENT) if self.tokens.last().unwrap().1.len() == 1 => {
                        self.parse_entry_footer();
                    }
                    _ => break,
                }
            }

            self.builder.finish_node();
        }

        pub fn parse_entry_detail(&mut self) {
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
        }

        pub fn parse_entry_footer(&mut self) {
            self.expect(INDENT);

            self.expect(DASHES);

            self.expect(WHITESPACE);

            self.builder.start_node(MAINTAINER.into());
            self.expect(TEXT);
            self.builder.finish_node();

            self.expect(WHITESPACE);

            self.builder.start_node(EMAIL.into());
            self.expect(TEXT);
            self.builder.finish_node();

            self.expect(WHITESPACE);
            self.expect(TEXT);
            self.expect(NEWLINE);
        }

        fn parse(mut self) -> Parse {
            // Make sure that the root node covers all source
            self.builder.start_node(ROOT.into());
            while self.current().is_some() {
                self.parse_entry();
            }
            // Don't forget to eat *trailing* whitespace
            self.skip_ws();
            // Close the root node.
            self.builder.finish_node();

            // Turn the builder into a GreenNode
            Parse {
                green_node: self.builder.finish(),
                errors: self.errors,
            }
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

/// To work with the parse results we need a view into the
/// green tree - the Syntax tree.
/// It is also immutable, like a GreenNode,
/// but it contains parent pointers, offsets, and
/// has identity semantics.

type SyntaxNode = rowan::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = rowan::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

impl Parse {
    fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }

    fn root(&self) -> ChangeLog {
        ChangeLog::cast(self.syntax()).unwrap()
    }
}

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(PartialEq, Eq, Hash)]
        #[repr(transparent)]
        pub struct $ast(SyntaxNode);
        impl $ast {
            #[allow(unused)]
            fn cast(node: SyntaxNode) -> Option<Self> {
                if node.kind() == $kind {
                    Some(Self(node))
                } else {
                    None
                }
            }
        }

        impl ToString for $ast {
            fn to_string(&self) -> String {
                self.0.text().to_string()
            }
        }
    };
}

ast_node!(ChangeLog, ROOT);
ast_node!(Entry, ENTRY);

impl ChangeLog {
    pub fn new() -> ChangeLog {
        let mut builder = GreenNodeBuilder::new();

        builder.start_node(ROOT.into());
        builder.finish_node();
        ChangeLog(SyntaxNode::new_root(builder.finish()))
    }

    /// Returns an iterator over all entries in the watch file.
    pub fn entries(&self) -> impl Iterator<Item = Entry> + '_ {
        self.0.children().filter_map(Entry::cast)
    }
}

impl FromStr for ChangeLog {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parsed = parse(s);
        if parsed.errors.is_empty() {
            Ok(parsed.root())
        } else {
            Err(ParseError(parsed.errors))
        }
    }
}

#[test]
fn test_parse_simple() {
    const CHANGELOG: &str = r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0000

breezy (3.3.3-2) unstable; urgency=medium

  * Drop unnecessary dependency on python3-six. Closes: #1039011
  * Drop dependency on cython3-dbg. Closes: #1040544

 -- Jelmer Vernooĳ <jelmer@debian.org>  Sat, 24 Jun 2023 14:58:57 +0100
"#;
    let parsed = parse(CHANGELOG);
    eprintln!("{:#?}", parsed.syntax());
    //assert_eq!(parsed.errors, Vec::<String>::new());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..156
  VERSION@0..10
    KEY@0..7 "version"
    EQUALS@7..8 "="
    VALUE@8..9 "4"
    NEWLINE@9..10 "\n"
  ENTRY@10..156
    OPTS_LIST@10..81
      KEY@10..14 "opts"
      EQUALS@14..15 "="
      OPTION@15..81
        KEY@15..29 "filenamemangle"
        EQUALS@29..30 "="
        VALUE@30..81 "s/.+\\/v?(\\d\\S+)\\.tar\\ ..."
    WHITESPACE@81..82 " "
    CONTINUATION@82..84 "\\\n"
    WHITESPACE@84..86 "  "
    VALUE@86..133 "https://github.com/sy ..."
    WHITESPACE@133..134 " "
    VALUE@134..155 ".*/v?(\\d\\S+)\\.tar\\.gz"
    NEWLINE@155..156 "\n"
"#
    );

    let root = parsed.root();

    assert_eq!(node.text(), CHANGELOG);
}
