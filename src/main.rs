#![warn(missing_docs)]

//! Main program
use std::process;

use bft_interp::{ContainsWriter, VM};
use bft_types::BFProgram;

mod cli;
use clap::Parser;
use cli::Args;
use std::io::{stdin, stdout, Write};

/// Run the interpreter, accepting CLI options
fn run_bft(args: &Args) -> Result<(), Box<dyn std::error::Error>> {
    let program = BFProgram::from_file(&args.file_name)?;
    let extend_auto;
    match args.extend_auto.as_str() {
        "n" => extend_auto = false,
        "y" => extend_auto = true,
        // TODO I could return an error here, but ideally I'd like to let the argument be a pure flag, not y/n.
        // Is this possible using clap's parser? I didn't seem to find much info on this.
        _ => return Ok(()),
    }
    let tape_size = args.num_cells.parse::<usize>()?;
    let mut vm: VM<u8> = VM::new(&program, tape_size, extend_auto);
    // I/O streams
    let output: Box<dyn Write> = Box::new(stdout());
    let mut wrapped_output = ContainsWriter {
        writer: output,
        last_character_newline: false,
    };
    let mut input = stdin();

    let ans = vm.interpret(&mut input, &mut wrapped_output);
    if let Err(e) = ans {
        return Err(Box::new(e));
    }
    Ok(())
}

/// Main function.
/// Parse the CLI argument and run interpreter

fn main() {
    let args = Args::parse();
    if let Err(e) = run_bft(&args) {
        eprintln!("Error in file {:?}: {}", args.file_name, e);
        process::exit(1);
    }
}
