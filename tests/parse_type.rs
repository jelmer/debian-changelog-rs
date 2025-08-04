use debian_changelog::{ChangeLog, Parse};

#[test]
fn test_parse_clone() {
    let changelog_text = r#"test (1.0.0) unstable; urgency=low

  * Initial release.

 -- Test User <test@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#;

    let parsed: Parse<ChangeLog> = ChangeLog::parse(changelog_text);
    let cloned = parsed.clone();

    // Verify that clone creates an equal object
    assert_eq!(parsed, cloned);

    // Verify they have the same content
    assert_eq!(parsed.green(), cloned.green());
    assert_eq!(parsed.errors(), cloned.errors());
}

#[test]
fn test_parse_partial_eq() {
    let changelog1 = r#"test (1.0.0) unstable; urgency=low

  * Initial release.

 -- Test User <test@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#;

    let changelog2 = r#"test (2.0.0) unstable; urgency=low

  * New version.

 -- Test User <test@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#;

    let parsed1 = ChangeLog::parse(changelog1);
    let parsed2 = ChangeLog::parse(changelog2);
    let parsed1_clone = parsed1.clone();

    // Same content should be equal
    assert_eq!(parsed1, parsed1_clone);

    // Different content should not be equal
    assert_ne!(parsed1, parsed2);
}

#[test]
fn test_parse_with_errors() {
    // Parse some invalid changelog
    let invalid_text = "this is not a valid changelog";
    let parsed = ChangeLog::parse(invalid_text);

    // Should have errors
    assert!(!parsed.ok());
    assert!(!parsed.errors().is_empty());

    // Clone should preserve errors
    let cloned = parsed.clone();
    assert_eq!(parsed.errors(), cloned.errors());
    assert_eq!(parsed, cloned);
}

#[test]
fn test_parse_errors_accessor() {
    let invalid_text = "INVALID";
    let parsed = ChangeLog::parse(invalid_text);

    // Access errors
    let errors = parsed.errors();
    assert!(!errors.is_empty());
    assert!(errors[0].contains("expected") || errors[0].contains("VERSION"));
}

#[test]
fn test_parse_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Parse<ChangeLog>>();
}

#[test]
fn test_parse_to_result_with_errors() {
    let invalid_text = "INVALID CHANGELOG";
    let parsed = ChangeLog::parse(invalid_text);

    // to_result should return Err when there are errors
    let result = parsed.to_result();
    assert!(result.is_err());

    match result {
        Err(_) => {
            // Expected error
        }
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

#[test]
fn test_parse_to_mut_result_with_errors() {
    let invalid_text = "INVALID CHANGELOG";
    let parsed = ChangeLog::parse(invalid_text);

    // to_mut_result should return Err when there are errors
    let result = parsed.to_mut_result();
    assert!(result.is_err());

    match result {
        Err(_) => {
            // Expected error
        }
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

#[test]
fn test_parse_tree_mut() {
    let changelog_text = r#"test (1.0.0) unstable; urgency=low

  * Initial release.

 -- Test User <test@example.com>  Mon, 04 Sep 2023 18:13:45 -0500
"#;

    let parsed = ChangeLog::parse(changelog_text);
    let tree = parsed.tree_mut();

    // Should be able to get a mutable tree
    assert_eq!(tree.iter().count(), 1);

    // Verify the content
    let entry = tree.iter().next().unwrap();
    assert_eq!(entry.package(), Some("test".to_string()));
    assert_eq!(entry.version().unwrap().to_string(), "1.0.0");
}

#[test]
#[should_panic(expected = "tried to get tree with errors")]
fn test_parse_tree_panics_with_errors() {
    let invalid_text = "INVALID";
    let parsed = ChangeLog::parse(invalid_text);

    // This should panic because there are errors
    let _tree = parsed.tree();
}

#[test]
#[should_panic(expected = "tried to get tree with errors")]
fn test_parse_tree_mut_panics_with_errors() {
    let invalid_text = "INVALID";
    let parsed = ChangeLog::parse(invalid_text);

    // This should panic because there are errors
    let _tree = parsed.tree_mut();
}

#[test]
fn test_parse_equality_with_same_errors() {
    // Two parses of the same invalid input should be equal
    let invalid_text = "INVALID CHANGELOG";
    let parsed1 = ChangeLog::parse(invalid_text);
    let parsed2 = ChangeLog::parse(invalid_text);

    assert_eq!(parsed1, parsed2);
}

#[test]
fn test_parse_inequality_different_errors() {
    // Different invalid inputs should produce different Parse objects
    let invalid1 = "INVALID1";
    let invalid2 = "INVALID2 (different)";

    let parsed1 = ChangeLog::parse(invalid1);
    let parsed2 = ChangeLog::parse(invalid2);

    // They should not be equal because they have different green nodes
    assert_ne!(parsed1, parsed2);
}
