#![warn(missing_docs)]

//! Main program
use std::{path, process};

use bft_interp::VM;
use bft_types::BFProgram;

mod cli;
use clap::Parser;
use cli::Options;
use std::io::{self, stdin, stdout, Read, Write};

/// Run the interpreter, accepting CLI options
fn run_bft(opt: &Options) -> Result<(), Box<dyn std::error::Error>> {
    let program = BFProgram::from_file(&opt.file_name)?;
    // TODO don't like how the path's type was automatically specified above, but had to be manually specified below. Is there a way to avoid this?
    let mut vm: VM<u8, &path::PathBuf> = VM::new(&program, 0, false);

    let mut output: Box<dyn Write> = Box::new(stdout());
    let mut input = stdin();

    let ans = vm.interpret(&mut input, &mut output);
    if let Err(e) = ans {
        return Err(Box::new(e));
    }
    Ok(())
}

/// Main function.
/// Parse the CLI argument and run interpreter

fn main() {
    let opt = Options::parse();
    if let Err(e) = run_bft(&opt) {
        eprintln!("Error in file {:?}: {}", opt.file_name, e);
        process::exit(1);
    }
}
