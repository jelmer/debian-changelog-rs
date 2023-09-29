//! Text wrapping functions
//!
//! These functions are used to wrap text for use in a changelog.
//! The main function is `textwrap`, which takes a string and wraps it to a
//! specified width, without breaking in between "Closes: #XXXXXX" fragments.

use lazy_regex::{regex, regex_captures};
use std::borrow::Cow;
use textwrap::core::Word;

pub const DEFAULT_WIDTH: usize = 78;
pub const INITIAL_INDENT: &str = "* ";

#[inline]
fn can_break_word(line: &str, pos: usize) -> bool {
    if let Some(_bugnp) = line.strip_prefix("Closes: #") {
        if pos < line.find('#').unwrap() {
            return false;
        }
    }
    if let Some(_lpbugno) = line.strip_prefix("LP: #") {
        if pos < line.find('#').unwrap() {
            return false;
        }
    }
    line[pos..].starts_with(' ')
}

#[cfg(test)]
mod can_break_word_tests {
    #[test]
    fn test_can_break_word() {
        assert!(super::can_break_word("foo bar", 3));
        assert!(!super::can_break_word("foo bar", 0));
        assert!(!super::can_break_word("foo bar", 5));
    }

    #[test]
    fn test_closes() {
        assert!(!super::can_break_word("Closes: #123456", 6));
        assert!(!super::can_break_word("Closes: #123456", 7));
        assert!(!super::can_break_word("Closes: #123456", 8));
        assert!(!super::can_break_word("Closes: #123456", 9));
        assert!(super::can_break_word("Closes: #123456 foo", 15));
    }
}

fn find_words<'a>(line: &'a str) -> Box<dyn Iterator<Item = Word<'a>> + 'a> {
    let mut start = 0;
    let mut can_break = false;
    let mut char_indices = line.char_indices();

    Box::new(std::iter::from_fn(move || {
        for (idx, ch) in char_indices.by_ref() {
            let word_finished = can_break && ch != ' ';
            can_break = can_break_word(&line[start..], idx - start);
            if word_finished {
                let word = Word::from(&line[start..idx]);
                start = idx;
                return Some(word);
            }
        }

        if start < line.len() {
            let word = Word::from(&line[start..]);
            start = line.len();
            return Some(word);
        }

        None
    }))
}

#[cfg(test)]
mod find_words_tests {
    use super::find_words;
    use textwrap::core::Word;
    use textwrap::WordSeparator;
    #[test]
    fn test_find_words() {
        let ws = WordSeparator::Custom(find_words);
        assert_eq!(
            vec![Word::from("foo")],
            ws.find_words("foo").collect::<Vec<_>>()
        );
        assert_eq!(
            vec![Word::from("foo "), Word::from("bar")],
            ws.find_words("foo bar").collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_split_closes() {
        let ws = WordSeparator::Custom(find_words);
        assert_eq!(
            vec![
                Word::from("This "),
                Word::from("test "),
                Word::from("Closes: #123456 "),
                Word::from("foo"),
            ],
            ws.find_words("This test Closes: #123456 foo")
                .collect::<Vec<_>>()
        );

        assert_eq!(
            vec![
                Word::from("This "),
                Word::from("test "),
                Word::from("Closes: #123456"),
            ],
            ws.find_words("This test Closes: #123456")
                .collect::<Vec<_>>()
        );
    }
}

/// Wrap a string of text, without breaking in between "Closes: #XXXXXX" fragments
pub fn textwrap<'a>(
    text: &'a str,
    width: Option<usize>,
    initial_indent: Option<&str>,
    subsequent_indent: Option<&str>,
) -> Vec<Cow<'a, str>> {
    let width = width.unwrap_or(DEFAULT_WIDTH);
    let mut options = textwrap::Options::new(width)
        .break_words(false)
        .word_splitter(textwrap::WordSplitter::NoHyphenation)
        .word_separator(textwrap::WordSeparator::Custom(find_words));
    if let Some(initial_indent) = initial_indent {
        options = options.initial_indent(initial_indent);
    }
    if let Some(subsequent_indent) = subsequent_indent {
        options = options.subsequent_indent(subsequent_indent);
    }
    // Actual text wrapping using textwrap crate
    textwrap::wrap(text, options)
}

#[cfg(test)]
mod textwrap_tests {
    #[test]
    fn test_wrap_closes() {
        assert_eq!(
            vec!["And", "this", "fixes", "something.", "Closes: #123456"],
            super::textwrap(
                "And this fixes something. Closes: #123456",
                Some(5),
                None,
                None
            )
        );
    }

    #[test]
    fn test_wrap() {
        let ws = textwrap::WordSeparator::Custom(super::find_words);
        let options = textwrap::Options::new(30)
            .break_words(false)
            .word_separator(ws);
        assert_eq!(
            vec!["This", "is", "a", "line", "that", "has", "been", "broken"],
            ws.find_words("This is a line that has been broken")
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            vec!["This is a line that has been", "broken"],
            textwrap::wrap("This is a line that has been broken", options)
        );

        assert_eq!(
            vec!["This is a line that has been", "broken"],
            super::textwrap("This is a line that has been broken", Some(30), None, None)
        );
    }
}
