//! Contains structs and methods for BF interpreter.
//! Currently just prints instructions.
#![warn(missing_docs)]

use bft_types::{BFProgram, InputInstruction};
use std::clone;
use std::cmp;
use std::path::Path;
use thiserror::Error;

/// Represents virtual machine: tape with some number of cells, each of some type.
/// Includes option to dynamically grow tape.
// TODO how to make this lifetime compatible with that of VM?
// I can't currently let VMError return a *reference* to an instruction
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

#[derive(Error, Debug, cmp::PartialEq)]
/// Enum for VM errors
pub enum VMError<'a, 'b> {
    #[error("Some error message TODO")]
    /// Bad bracket error type
    InvalidHead {
        /// Error description
        error_desciption: &'a str,
        /// Instruction causing error
        bad_instruction: &'b InputInstruction,
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
    /// Move head left
    /// TODO add for being *allowed* to move head
    pub fn move_head_left(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        if self.data_head == 0 {
            return Err(VMError::InvalidHead {
                error_desciption: "Head already at leftmost position",
                bad_instruction: i,
            });
        }
        self.data_head -= 1;
        // TODO remove this, used for debugging
        Ok(())
    }
    /// Move head right
    /// TODO add tests
    pub fn move_head_right(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        // TODO implementation
        if self.data_head == self.num_cells - 1 {
            return Err(VMError::InvalidHead {
                error_desciption: "Head already at rightmost position",
                bad_instruction: i,
            });
        }
        self.data_head += 1;
        Ok(())
    }
}

#[cfg(test)]

mod tests {

    use super::VMError;
    use bft_types::{InputInstruction, RawInstruction};

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

    #[test]
    fn pointer_left_fail() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<usize, &str> = VM::new(&p, 0, false);
        //assert_eq!(vm.data_head, 0);
        let ans = vm.move_head_left(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidHead {
                error_desciption: "Head already at leftmost position",
                bad_instruction: &InputInstruction::new(RawInstruction::PointerDec, 2, 3)
            })
        );
    }
    #[test]
    fn pointer_right_fail() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<usize, &str> = VM::new(&p, 0, false);
        //assert_eq!(vm.data_head, 0);
        let mut _ans;
        for n in (0..vm.num_cells() - 1) {
            _ans = vm.move_head_right(i);
        }
        let ans = vm.move_head_right(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidHead {
                error_desciption: "Head already at rightmost position",
                bad_instruction: &InputInstruction::new(RawInstruction::PointerDec, 2, 3)
            })
        );
    }
    #[test]
    fn pointer_right_left_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<usize, &str> = VM::new(&p, 0, false);
        assert_eq!(vm.data_head, 0);
        let mut _ans;
        for n in (0..10) {
            _ans = vm.move_head_right(i);
        }
        assert_eq!(vm.data_head, 10);
        for n in (0..5) {
            _ans = vm.move_head_left(i);
        }
        assert_eq!(vm.data_head, 5);
    }
}
