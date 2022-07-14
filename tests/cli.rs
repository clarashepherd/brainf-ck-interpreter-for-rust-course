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
/// Create VM with 1 cell, read in 'hello world' and have auto-expand
fn hello_world_auto_expand() -> Result<(), Box<dyn std::error::Error>> {
    let temp_file = assert_fs::NamedTempFile::new("helloWorld.txt")?;
    temp_file.write_str(
        ">++++++++[<+++++++++>-]<.>++++[<+++++++>-]<+.+++++++..+++.>>++++++[<+++++++>-]<+
    +.------------.>++++++[<+++++++++>-]<+.<.+++.------.--------.>>>++++[<++++++++>-
    ]<+.",
    )?;
    // Run binary
    let mut cmd = Command::cargo_bin("bft")?;
    cmd.arg(temp_file.path());
    cmd.arg("-n");
    cmd.arg("1");
    cmd.arg("-e");
    cmd.assert().success().stdout("Hello, World!\n");
    Ok(())
}

// Auto-expand off, check for failure
#[test]
/// Create VM with 1 cell, read in 'hello world' w/o auto expand.
/// Expect failure due to tape being too small.
fn hello_world_size_fail() -> Result<(), Box<dyn std::error::Error>> {
    let temp_file = assert_fs::NamedTempFile::new("helloWorld.txt")?;
    temp_file.write_str(
        ">++++++++[<+++++++++>-]<.>++++[<+++++++>-]<+.+++++++..+++.>>++++++[<+++++++>-]<+
    +.------------.>++++++[<+++++++++>-]<+.<.+++.------.--------.>>>++++[<++++++++>-
    ]<+.",
    )?;
    // Run binary
    let mut cmd = Command::cargo_bin("bft")?;
    cmd.arg(temp_file.path());
    cmd.arg("-n");
    cmd.arg("1");
    cmd.assert().failure().stderr(format!("Error in file \"{}\": Invalid head position: can\'t exceed rightmost position, bad instruction: [1:1] Increment data pointer\n", temp_file.path().display()));
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
        "Error in file \"{}\": Bracket not closed. Type is ], line 1, col 3\n",
        temp_file.path().display()
    ));
    Ok(())
}
