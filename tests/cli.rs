// Integration tests

use assert_cmd::prelude::*;
use assert_fs::prelude::*;
use std::process::Command; // Run programs // Add methods on commands

#[test]
fn hello_world() -> Result<(), Box<dyn std::error::Error>> {
    let temp_file = assert_fs::NamedTempFile::new("helloWorld.txt")?;
    temp_file.write_str(
        ">++++++++[<+++++++++>-]<.>++++[<+++++++>-]<+.+++++++..+++.>>++++++[<+++++++>-]<+
        +.------------.>++++++[<+++++++++>-]<+.<.+++.------.--------.>>>++++[<++++++++>-
        ]<+.",
    )?;
    // Run binary
    let mut cmd = Command::cargo_bin("bft")?;
    cmd.arg(temp_file.path());
    cmd.assert().success().stdout("Hello, World!");
    Ok(())
}
