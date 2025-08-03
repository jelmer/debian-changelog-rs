use debian_changelog::{Error, ParseError};
use std::io;

#[test]
fn test_error_display() {
    // Test IO error display
    let io_error = io::Error::new(io::ErrorKind::NotFound, "file not found");
    let error = Error::Io(io_error);
    let display = format!("{}", error);
    assert!(display.contains("IO error"));
    assert!(display.contains("file not found"));
    
    // Test Parse error display
    let parse_error = ParseError::from(vec!["syntax error".to_string()]);
    let error = Error::Parse(parse_error);
    let display = format!("{}", error);
    assert!(display.contains("Parse error"));
    assert!(display.contains("syntax error"));
}

#[test]
fn test_parse_error_display() {
    // Test single error
    let error = ParseError::from(vec!["invalid version".to_string()]);
    let display = format!("{}", error);
    assert_eq!(display.trim(), "invalid version");
    
    // Test multiple errors
    let error = ParseError::from(vec![
        "error 1".to_string(),
        "error 2".to_string(),
        "error 3".to_string(),
    ]);
    let display = format!("{}", error);
    assert!(display.contains("error 1"));
    assert!(display.contains("error 2"));
    assert!(display.contains("error 3"));
}

#[test]
fn test_parse_error_from_vec() {
    let errors = vec!["test error".to_string()];
    let parse_error = ParseError::from(errors);
    let display = format!("{}", parse_error);
    assert_eq!(display.trim(), "test error");
}