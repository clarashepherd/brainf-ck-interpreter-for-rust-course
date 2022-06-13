#![warn(missing_docs)]

//! Main program
use std::{path, process};

use bft_interp::VM;
use bft_types::BFProgram;

mod cli;
use clap::Parser;
use cli::Options;

/// Run the interpreter, accepting CLI options
fn run_bft(opt: &Options) -> Result<(), Box<dyn std::error::Error>> {
    let program = BFProgram::from_file(&opt.file_name)?;
    let vm: VM<usize, &path::PathBuf> = VM::new(&program, 0, false);
    vm.interpret(&program);

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
