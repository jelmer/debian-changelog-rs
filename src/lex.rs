use create::SyntaxKind;
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum LineType {
    Header,
    Body,
    Footer,
}

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    line_type: Option<LineType>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input: input.chars().peekable(),
            line_type: None,
        }
    }

    fn is_whitespace(c: char) -> bool {
        c == ' ' || c == '\t'
    }

    fn is_newline(c: char) -> bool {
        c == '\n' || c == '\r'
    }

    fn is_valid_identifier_char(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '-' || c == '.'
    }

    fn read_while<F>(&mut self, predicate: F) -> String
    where
        F: Fn(char) -> bool,
    {
        let mut result = String::new();
        while let Some(&c) = self.input.peek() {
            if predicate(c) {
                result.push(c);
                self.input.next();
            } else {
                break;
            }
        }
        result
    }

    fn read_while_n<F>(&mut self, n: usize, predicate: F) -> String
    where
        F: Fn(char) -> bool,
    {
        let mut result = String::new();
        while let Some(&c) = self.input.peek() {
            if predicate(c) {
                result.push(c);
                self.input.next();

                if result.len() >= n {
                    break;
                }
            } else {
                break;
            }
        }
        result
    }

    fn next_token(&mut self) -> Option<(SyntaxKind, String)> {
        if let Some(&c) = self.input.peek() {
            match (c, self.line_type) {
                (c, None) | (c, Some(LineType::Header)) if Self::is_valid_identifier_char(c) => {
                    let identifier = self.read_while(Self::is_valid_identifier_char);
                    self.line_type = Some(LineType::Header);
                    Some((SyntaxKind::IDENTIFIER, identifier))
                }
                (c, None) if Self::is_whitespace(c) => {
                    let mut indent = self.read_while_n(2, |c| c == ' ');
                    if indent.len() == 1 {
                        let dashes = self.read_while(|c| c == '-' || c == ' ');
                        indent.push_str(dashes.as_str());
                        self.line_type = Some(LineType::Footer);
                    } else {
                        self.line_type = Some(LineType::Body);
                    }
                    Some((SyntaxKind::INDENT, indent))
                }
                ('#', None) => {
                    let comment = self.read_while(|c| !Self::is_newline(c));
                    let n = self.input.next();
                    if let Some(n) = n {
                        Some((SyntaxKind::COMMENT, comment + n.to_string().as_str()))
                    } else {
                        Some((SyntaxKind::COMMENT, comment))
                    }
                }
                (c, _) if Self::is_newline(c) => {
                    self.input.next();
                    self.line_type = None;
                    Some((SyntaxKind::NEWLINE, c.to_string()))
                }
                (';', Some(LineType::Header)) => Some((
                    SyntaxKind::SEMICOLON,
                    self.input.next().unwrap().to_string(),
                )),
                ('(', Some(LineType::Header)) => {
                    let version = self
                        .read_while(|c| c != ')' && c != ';' && c != ' ' && !Self::is_newline(c));
                    let n = self.input.next();
                    if n == Some(')') {
                        Some((
                            SyntaxKind::VERSION,
                            version + n.unwrap().to_string().as_str(),
                        ))
                    } else if let Some(n) = n {
                        Some((SyntaxKind::ERROR, version + n.to_string().as_str()))
                    } else {
                        Some((SyntaxKind::ERROR, version))
                    }
                }
                ('=', Some(LineType::Header)) => {
                    Some((SyntaxKind::EQUALS, self.input.next().unwrap().to_string()))
                }
                (_, Some(LineType::Body)) => {
                    let detail = self.read_while(|c| !Self::is_newline(c));
                    Some((SyntaxKind::DETAIL, detail))
                }
                (c, _) if Self::is_whitespace(c) => {
                    let ws = self.read_while(Self::is_whitespace);
                    Some((SyntaxKind::WHITESPACE, ws))
                }

                ('<', Some(LineType::Footer)) => {
                    let email = self.read_while(|c| c != '>' && c != ' ' && !Self::is_newline(c));
                    let n = self.input.next();
                    if n == Some('>') {
                        Some((SyntaxKind::EMAIL, email + n.unwrap().to_string().as_str()))
                    } else if let Some(n) = n {
                        Some((SyntaxKind::ERROR, email + n.to_string().as_str()))
                    } else {
                        Some((SyntaxKind::ERROR, email))
                    }
                }
                (c, Some(LineType::Footer)) if !Self::is_whitespace(c) && !Self::is_newline(c) => {
                    let identifier =
                        self.read_while(|c| c != ' ' && c != '<' && !Self::is_newline(c));
                    Some((SyntaxKind::TEXT, identifier))
                }
                (_, _) => {
                    self.input.next();
                    Some((SyntaxKind::ERROR, c.to_string()))
                }
            }
        } else {
            None
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = (create::SyntaxKind, String);

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}

pub(create) fn lex(input: &str) -> Vec<(SyntaxKind, String)> {
    let mut lexer = Lexer::new(input);
    lexer.by_ref().collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use create::SyntaxKind::*;
    #[test]
    fn test_empty() {
        assert_eq!(super::lex(""), vec![]);
    }

    #[test]
    fn test_simple() {
        assert_eq!(
            super::lex(
                r#"breezy (3.3.4-1) unstable; urgency=low

  * New upstream release.

 -- Jelmer Vernooĳ <jelmer@debian.org>  Mon, 04 Sep 2023 18:13:45 -0000

# Oh, and here is a comment
"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "breezy"),
                (WHITESPACE, " "),
                (VERSION, "(3.3.4-1)"),
                (WHITESPACE, " "),
                (IDENTIFIER, "unstable"),
                (SEMICOLON, ";"),
                (WHITESPACE, " "),
                (IDENTIFIER, "urgency"),
                (EQUALS, "="),
                (IDENTIFIER, "low"),
                (NEWLINE, "\n"),
                (NEWLINE, "\n"),
                (INDENT, "  "),
                (DETAIL, "* New upstream release."),
                (NEWLINE, "\n"),
                (NEWLINE, "\n"),
                (INDENT, " -- "),
                (TEXT, "Jelmer"),
                (WHITESPACE, " "),
                (TEXT, "Vernooĳ"),
                (WHITESPACE, " "),
                (EMAIL, "<jelmer@debian.org>"),
                (WHITESPACE, "  "),
                (TEXT, "Mon,"),
                (WHITESPACE, " "),
                (TEXT, "04"),
                (WHITESPACE, " "),
                (TEXT, "Sep"),
                (WHITESPACE, " "),
                (TEXT, "2023"),
                (WHITESPACE, " "),
                (TEXT, "18:13:45"),
                (WHITESPACE, " "),
                (TEXT, "-0000"),
                (NEWLINE, "\n"),
                (NEWLINE, "\n"),
                (COMMENT, "# Oh, and here is a comment\n"),
            ]
        );
    }
}
