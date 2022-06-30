// Integration tests

use assert_cmd::prelude::*;
use assert_fs::prelude::*;
use std::process::Command; // Run programs // Add methods on commands

#[test]
/// Run 'hello world' program
fn hello_world_ok() -> Result<(), Box<dyn std::error::Error>> {
    let temp_file = assert_fs::NamedTempFile::new("helloWorld.txt")?;
    temp_file.write_str(
        ">++++++++[<+++++++++>-]<.>++++[<+++++++>-]<+.+++++++..+++.>>++++++[<+++++++>-]<+
        +.------------.>++++++[<+++++++++>-]<+.<.+++.------.--------.>>>++++[<++++++++>-
        ]<+.",
    )?;
    // Run binary
    let mut cmd = Command::cargo_bin("bft")?;
    cmd.arg(temp_file.path());
    cmd.assert().success().stdout("Hello, World!\n");
    Ok(())
}

#[test]
/// File doesn't exist, print an error message
fn file_does_not_exist() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("bft")?;
    cmd.arg("path/does/not/exist");
    cmd.assert()
        .failure()
        .stderr("Error in file \"path/does/not/exist\": No such file or directory (os error 2)\n");
    Ok(())
}

#[test]
/// Mismatched brackets, print an error message
fn mismatched_brackets() -> Result<(), Box<dyn std::error::Error>> {
    let temp_file = assert_fs::NamedTempFile::new("helloWorld.txt")?;
    temp_file.write_str("[]]")?;
    // Run binary
    let mut cmd = Command::cargo_bin("bft")?;
    cmd.arg(temp_file.path());
    cmd.assert().failure().stderr(format!(
        "Error in file \"{}\": Bracket not closed. Type is ]\n",
        temp_file.path().display()
    ));
    Ok(())
}

// TODO test user input functionality
