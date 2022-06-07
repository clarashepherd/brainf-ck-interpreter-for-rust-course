#![warn(missing_docs)]

//! Main program
use bft_interp::VM;
use bft_types::BFProgram;
use std::env;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Nice syntax taken from Nathan's solution
    // ok_or: converts Option<T> into Result<T,E>
    let file_name = env::args().nth(1).ok_or("No file name provided")?;

    // How could the error propagation for opening the file be put into
    // bft_types/src/lib.rs?
    let prog = BFProgram::from_file(file_name)?;
    let vm: VM<usize> = VM::new(0, false);
    // Print output
    vm.interpret(&prog);

    Ok(())
}
