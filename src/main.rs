#![warn(missing_docs)]

//! Main program
use bft_interp::VM;
use bft_types::BFProgram;
use std::path::PathBuf;

mod cli;
use clap::Parser;
use cli::Options;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Options::parse();
    let prog = BFProgram::from_file(opt.file_name)?;
    let vm: VM<usize> = VM::new(0, false);
    // Print output
    vm.interpret(&prog);

    Ok(())
}
