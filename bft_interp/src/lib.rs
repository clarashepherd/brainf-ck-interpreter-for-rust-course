//! Contains structs and methods for BF interpreter.
//! Currently just prints instructions.
#![warn(missing_docs)]

use bft_types::{BFProgram, RawInstruction};
use std::clone;
use std::path::Path;
use thiserror::Error;

/// Represents virtual machine: tape with some number of cells, each of some type.
/// Includes option to dynamically grow tape.
pub struct VM<'a, T, P>
where
    // Satisfies base trait for numeric types, and clone
    T: num_traits::Num + clone::Clone,
    P: AsRef<Path>,
{
    /// Borrow of program TOOD why
    prog: &'a BFProgram<P>,
    /// Number of cells
    num_cells: usize,
    /// Location of data pointer's head
    data_head: usize,
    /// Location of instruction pointer (program counter)
    instruction_head: usize,
    /// Tape
    tape: Vec<T>,
    /// Is tape allowed to dynamically grow?
    can_grow: bool,
}

#[derive(Error, Debug, PartialEq)]
/// Enum for VM errors
pub enum VMError {
    #[error("Some error message TODO")]
    /// Bad bracket error type
    InvalidHead {
        /// Error description
        error_desciption: String,
        /// Instruction causing error
        bad_instruction: RawInstruction,
    },
}

// Note: T: ... syntax equivalent to a 'where'
impl<'a, T: num_traits::Num + clone::Clone, P: AsRef<Path>> VM<'a, T, P> {
    /// Get program
    pub fn prog(&'a self) -> &BFProgram<P> {
        self.prog
    }
    /// Get number of cells
    pub fn num_cells(&self) -> usize {
        self.num_cells
    }
    /// Get tape
    pub fn tape(&self) -> &Vec<T> {
        &self.tape
    }
    /// Get cangrow
    pub fn can_grow(&self) -> bool {
        self.can_grow
    }
    /// Get head pos
    pub fn data_head(&self) -> usize {
        self.data_head
    }
    /// Get instruction head
    pub fn instruction_head(&self) -> usize {
        self.instruction_head
    }
    /// Create new VM with some size, can choose whether to grow.
    /// If given size is zero, tape is 30,000 bytes long.
    pub fn new(prog: &'a BFProgram<P>, size: usize, can_grow: bool) -> Self {
        let mut num_cells = 30000;
        if size != 0 {
            num_cells = size;
        };
        let tape = Vec::with_capacity(num_cells);
        Self {
            prog,
            num_cells,
            tape,
            can_grow,
            data_head: 0,
            instruction_head: 0,
        }
    }

    /// Interpret the instructions at some given path.
    /// Currently just prints their content.
    pub fn interpret(&self, prog: &BFProgram<P>) {
        // "instructions" are private data, needed a getter method
        for i in prog.instructions() {
            println!("{}", i);
        }
    }
}

#[cfg(test)]

mod tests {

    use crate::BFProgram;
    use crate::VM;

    #[test]
    fn test_interpret() {
        // Not really a test. Just for debugging.
        // Need `-- --nocapture` to view output
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let vm: VM<usize, &str> = VM::new(&p, 0, false);
        vm.interpret(vm.prog);
    }
}
