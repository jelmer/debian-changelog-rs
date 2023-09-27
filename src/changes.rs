//! Functions to parse the changes from a changelog entry.

use lazy_regex::regex_captures;

#[derive(Default, Debug, PartialEq, Eq)]
struct SectionInfo<'a> {
    title: Option<&'a str>,
    linenos: Vec<usize>,
    changes: Vec<Vec<(usize, &'a str)>>,
}

/// Return the different sections from a set of changelog entries.
///
/// # Arguments
/// * `changes`: list of changes from a changelog entry
///
/// # Returns
///
/// An iterator over tuples with:
///    (author, list of line numbers, list of list of (lineno, line) tuples
fn changes_sections<'a>(
    changes: impl Iterator<Item = &'a str>,
) -> impl Iterator<Item = SectionInfo<'a>> {
    let mut ret: Vec<SectionInfo<'a>> = vec![];
    let mut section = SectionInfo::<'a>::default();
    let mut change = Vec::<(usize, &'a str)>::new();

    for (i, line) in changes.enumerate() {
        if line.is_empty() && i == 0 {
            // Skip the first line
            continue;
        }

        if line.is_empty() {
            section.linenos.push(i);
            continue;
        }

        if let Some((_, author)) = regex_captures!(r"^\[ (.*) \]$", line) {
            if !change.is_empty() {
                section.changes.push(change);
                change = Vec::new();
            }
            if !section.linenos.is_empty() {
                ret.push(section);
            }
            section = SectionInfo {
                title: Some(author),
                linenos: vec![i],
                changes: vec![],
            };
        }

        if !line.starts_with("* ") {
            change.push((i, line));
            section.linenos.push(i);
        } else {
            if !change.is_empty() {
                section.changes.push(change);
            }
            change = vec![(i, line)];
            section.linenos.push(i);
        }
    }
    if !change.is_empty() {
        section.changes.push(change);
    }
    if !section.linenos.is_empty() {
        ret.push(section);
    }

    ret.into_iter()
}

pub fn changes_by_author<'a>(
    changes: impl Iterator<Item = &'a str>,
) -> impl Iterator<Item = (Option<&'a str>, Vec<usize>, Vec<&'a str>)> {
    changes_sections(changes)
        .into_iter()
        .map(|section| {
            section
                .changes
                .into_iter()
                .map(|change_entry| {
                    let (linenos, lines): (Vec<_>, Vec<_>) = change_entry.into_iter().unzip();
                    (section.title, linenos, lines)
                })
                .collect::<Vec<_>>()
        })
        .flatten()
}

#[cfg(test)]
mod changes_sections_tests {
    #[test]
    fn test_simple() {
        let iter = super::changes_sections(
            vec!["", "  * Change 1", "  * Change 2", "    rest", ""].into_iter(),
        );
        assert_eq!(
            vec![super::SectionInfo {
                title: None,
                linenos: vec![1, 2, 3, 4],
                changes: vec![
                    (vec![(1, "  * Change 1")]),
                    (vec![(2, "  * Change 2"), (3, "    rest")])
                ]
            }],
            iter.collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_with_header() {
        assert_eq!(
            vec![
                super::SectionInfo {
                    title: Some("Author 1"),
                    linenos: vec![1, 2, 3],
                    changes: vec![(vec![(2, "  * Change 1")])]
                },
                super::SectionInfo {
                    title: Some("Author 2"),
                    linenos: vec![4, 5, 6, 7],
                    changes: vec![(vec![(5, "  * Change 2"), (6, "    rest")])]
                },
            ],
            super::changes_sections(
                vec![
                    "",
                    "  [ Author 1 ]",
                    "  * Change 1",
                    "",
                    "  [ Author 2 ]",
                    "  * Change 2",
                    "    rest",
                    "",
                ]
                .into_iter()
            )
            .collect::<Vec<_>>()
        );
    }
}
