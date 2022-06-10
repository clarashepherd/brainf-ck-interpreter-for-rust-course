//! Contains structs and methods for BF interpreter.
//! Currently just prints instructions.
#![warn(missing_docs)]

use bft_types::BFProgram;
use std::path::Path;

/// Represents virtual machine: tape with some number of cells, each of some type.
/// Includes option to dynamically grow tape.
pub struct VM<T> {
    /// Number of cells
    num_cells: usize,
    /// Tape
    tape: Vec<T>,
    // Is tape allowed to dynamically grow?
    can_grow: bool,
}
impl<T> VM<T> {
    /// Getter for number of cells
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
    /// Create new VM with some size, can choose whether to grow.
    /// If given size is zero, tape is 30,000 bytes long.
    pub fn new(size: usize, can_grow: bool) -> Self {
        let mut num_cells = 30000;
        if size != 0 {
            num_cells = size;
        };
        let tape = Vec::with_capacity(num_cells);
        Self {
            num_cells,
            tape,
            can_grow,
        }
    }

    /// Interpret the instructions at some given path.
    /// Currently just prints their content.
    pub fn interpret<P: AsRef<Path>>(self, prog: &BFProgram<P>) {
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
        let prog = BFProgram::new("TestFile", "<>.hello.".to_string());
        let vm: VM<usize> = VM::new(0, false);
        vm.interpret(&prog);
    }
}
