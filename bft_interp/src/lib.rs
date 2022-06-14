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
    #[error("Another error message TODO")]
    /// Oversize/negative error type
    InvalidValue {
        /// Error description
        error_description: &'a str,
        /// Instruction causing error
        bad_instruction: &'b InputInstruction,
    },
}

#[derive(Error, Debug)]
pub enum SizeError {
    #[error("Some error message TODO")]
    TooLarge,
    #[error("Another error message TODO")]
    TooSmall,
}

/// CellKind trait
/// Implements additon and subtraction
/// If can't add/subtract any further, returns modulus
/// e.g. 255+1 = 0
pub trait CellKind {
    /// Increment value by one
    fn inc_value(&self) -> Result<Self, SizeError>
    where
        Self: std::marker::Sized;
    /// Decrement value by one
    fn sub_value(&self) -> Result<Self, SizeError>
    where
        Self: std::marker::Sized;
}

impl CellKind for u8 {
    fn inc_value(&self) -> Result<Self, SizeError> {
        let ans = self.wrapping_add(1);
        // Note: had an error here.
        // Was testing (ans-self <0), but u8 can't be negative
        if &ans < self {
            println!("Returning size error");
            return Err(SizeError::TooLarge);
        }
        Ok(ans)
    }
    fn sub_value(&self) -> Result<Self, SizeError> {
        let ans = self.wrapping_sub(1);
        // TODO comment
        if &ans > self {
            println!("Returning size error");
            return Err(SizeError::TooSmall);
        }
        Ok(ans)
    }
}

// Note: "T: something satisfying CellKind trait"
// Only u8 satisfies CellKind, so T must currently be a u8
// Note: T: ... syntax equivalent to a 'where'
impl<'a, T: num_traits::Num + clone::Clone + CellKind + std::default::Default, P: AsRef<Path>>
    VM<'a, T, P>
{
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
    /// Get value at data head
    pub fn head_value(&self) -> &T {
        &self.tape[self.data_head]
    }
    /// Create new VM with some size, can choose whether to grow.
    /// If given size is zero, tape is 30,000 bytes long.
    pub fn new(prog: &'a BFProgram<P>, size: usize, can_grow: bool) -> Self {
        let mut num_cells = 30000;
        if size != 0 {
            num_cells = size;
        };
        let tape: Vec<T> = vec![Default::default(); num_cells];
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
    pub fn move_head_left(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        if self.data_head == 0 {
            return Err(VMError::InvalidHead {
                error_desciption: "Head already at leftmost position",
                bad_instruction: i,
            });
        }
        self.data_head -= 1;
        Ok(())
    }
    /// Move head right
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
    /// Increment value at a particular position, returning an error if value is too high
    pub fn increment_value(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        // TODO test
        let new_value = self.tape[self.data_head].inc_value();
        // If returns error, then test
        match new_value {
            Err(e) => {
                println!("FAILED");
                return Err(VMError::InvalidValue {
                    error_description: "Value too large for data type",
                    bad_instruction: i,
                });
            }
            Ok(ans) => {
                println!("OK");
                self.tape[self.data_head] = ans;
            }
        }
        Ok(())
    }
    /// Decrement value at particular position, returning an error if less than zero
    pub fn decrement_value(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        // TODO test
        let new_value = self.tape[self.data_head].sub_value();
        // If returns error, then test
        match new_value {
            Err(e) => {
                println!("FAILED");
                return Err(VMError::InvalidValue {
                    error_description: "Value cannot be smaller than zero",
                    bad_instruction: i,
                });
            }
            Ok(ans) => {
                println!("OK");
                self.tape[self.data_head] = ans;
            }
        }
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
        // Not really a test. Just for debugging with "-- --nocapture"
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let vm: VM<u8, &str> = VM::new(&p, 0, false);
        vm.interpret(vm.prog);
    }

    #[test]
    /// Check for failure when pointer goes too far left
    fn pointer_left_fail() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u8, &str> = VM::new(&p, 0, false);
        assert_eq!(vm.data_head, 0);
        let ans = vm.move_head_left(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidHead {
                error_desciption: "Head already at leftmost position",
                bad_instruction: i
            })
        );
    }

    #[test]
    /// Check for failure when pointer goes too far
    fn pointer_right_fail() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u8, &str> = VM::new(&p, 0, false);
        assert_eq!(vm.data_head, 0);
        let mut _ans;
        for _n in 0..vm.num_cells() - 1 {
            _ans = vm.move_head_right(i);
        }
        let ans = vm.move_head_right(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidHead {
                error_desciption: "Head already at rightmost position",
                bad_instruction: i
            })
        );
    }

    #[test]
    fn pointer_right_left_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u8, &str> = VM::new(&p, 0, false);
        assert_eq!(vm.data_head, 0);
        let mut _ans;
        for _n in 0..10 {
            _ans = vm.move_head_right(i);
        }
        assert_eq!(vm.data_head, 10);
        for _n in 0..5 {
            _ans = vm.move_head_left(i);
        }
        assert_eq!(vm.data_head, 5);
    }

    #[test]
    fn data_inc_dec_ok_fail_high() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u8, &str> = VM::new(&p, 0, false);
        assert_eq!(vm.data_head(), 0);
        assert_eq!(vm.tape[vm.data_head], 0);
        // Increase to max size
        for _n in 0..255 {
            let _ans = vm.increment_value(i);
        }
        assert_eq!(vm.head_value(), &255);
        // Decrease by one
        let _ans = vm.decrement_value(i);
        assert_eq!(vm.head_value(), &254);
        // Increase by one
        let _ans = vm.increment_value(i);
        assert_eq!(vm.head_value(), &255);
        // Increase past max size
        let ans = vm.increment_value(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidValue {
                error_description: "Value too large for data type",
                bad_instruction: i
            })
        );
    }

    #[test]
    fn data_dec_fail_low() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u8, &str> = VM::new(&p, 0, false);
        assert_eq!(vm.data_head(), 0);
        assert_eq!(vm.tape[vm.data_head], 0);
        // Try to decrease below zero
        let ans = vm.decrement_value(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidValue {
                error_description: "Value cannot be smaller than zero",
                bad_instruction: i
            })
        );
    }
}
