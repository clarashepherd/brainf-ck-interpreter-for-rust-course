//! Contains structs and methods for BF interpreter.
//! Currently just prints instructions.
#![warn(missing_docs)]

use bft_types::{BFProgram, InputInstruction};
use std::clone;
use std::cmp;
use std::convert;
use std::io::{Read, Write};
use std::path::Path;
use thiserror::Error;

/// Represents virtual machine: tape with some number of cells, each of some type.
/// Includes option to dynamically grow tape.
// TODO how to make this lifetime compatible with that of VM?
// I can't currently let VMError return a *reference* to an instruction
pub struct VM<'a, T, P>
where
    // Satisfies base trait for numeric types, and clone
    T: num_traits::Num + clone::Clone + convert::From<u8>,
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
    #[error(
        "Invalid head position: {}, bad instruction: {}",
        error_description,
        bad_instruction
    )]
    /// Bad bracket error type
    InvalidHead {
        /// Error description
        error_description: &'a str,
        /// Instruction causing error
        bad_instruction: &'b InputInstruction,
    },
    #[error(
        "Invalid head position: {}, bad instruction: {}",
        error_description,
        bad_instruction
    )]
    /// Oversize/negative error type
    InvalidData {
        /// Error description
        error_description: &'a str,
        /// Instruction causing error
        bad_instruction: &'b InputInstruction,
    },
    #[error("I/O error, bad instruction: {}", bad_instruction)]
    /// I/O errors from reader/writer functionality
    IOError {
        /// Eror desscription
        error_desciption: &'a str,
        /// Instruction causing error
        bad_instruction: &'b InputInstruction,
    },
}

#[derive(Error, Debug)]
/// Error returned when attempting to increase data pointer's value beyond tape size,
/// or below zero
pub enum TapeSizeError {
    /// Too large
    #[error("Value too large for tape's data type")]
    TooLarge,
    /// Too small
    #[error("Value too small for tape's data type (ie negative if unsigned)")]
    TooSmall,
}

/// CellKind trait
/// Implements additon and subtraction
/// If can't add/subtract any further, returns modulus
/// e.g. 255+1 = 0
pub trait CellKind {
    /// Increment value by one
    fn inc_value(&self) -> Result<Self, TapeSizeError>
    where
        Self: std::marker::Sized;
    /// Decrement value by one
    fn sub_value(&self) -> Result<Self, TapeSizeError>
    where
        Self: std::marker::Sized;
}

impl CellKind for u8 {
    fn inc_value(&self) -> Result<Self, TapeSizeError> {
        let ans = self.wrapping_add(1);
        // Addition and subtraction is mod(u8::SIZE)
        if &ans < self {
            return Err(TapeSizeError::TooLarge);
        }
        Ok(ans)
    }
    fn sub_value(&self) -> Result<Self, TapeSizeError> {
        let ans = self.wrapping_sub(1);
        // Addition and subtraction is mod(u8::SIZE)
        if &ans > self {
            return Err(TapeSizeError::TooSmall);
        }
        Ok(ans)
    }
}

impl CellKind for u16 {
    // TODO this was copied from above, only type changed.
    // Is there a way to avoid this duplication?
    fn inc_value(&self) -> Result<Self, TapeSizeError> {
        let ans = self.wrapping_add(1);
        // Addition and subtraction is mod(u16::SIZE)
        if &ans < self {
            return Err(TapeSizeError::TooLarge);
        }
        Ok(ans)
    }
    fn sub_value(&self) -> Result<Self, TapeSizeError> {
        let ans = self.wrapping_sub(1);
        // Addition and subtraction is mod(u8::SIZE)
        if &ans > self {
            return Err(TapeSizeError::TooSmall);
        }
        Ok(ans)
    }
}

/// Trait for "can get the first byte"
pub trait FirstByte {
    /// Returns first byte of some multi-byte number type
    fn first_byte(&self) -> u8;
}

impl FirstByte for u8 {
    fn first_byte(&self) -> u8 {
        *self
    }
}
impl FirstByte for u16 {
    fn first_byte(&self) -> u8 {
        self.to_be_bytes()[0]
    }
}

// Note: T: ... syntax equivalent to a 'where'
impl<
        'a,
        T: num_traits::Num
            + clone::Clone
            + CellKind
            + std::default::Default
            + convert::From<u8>
            + FirstByte,
        P: AsRef<Path>,
    > VM<'a, T, P>
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
    pub fn head_value(&mut self) -> &T {
        &mut self.tape[self.data_head]
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
                error_description: "can't be below zero",
                bad_instruction: i,
            });
        }
        self.data_head -= 1;
        Ok(())
    }
    /// Move head right
    pub fn move_head_right(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        if self.data_head == self.num_cells - 1 {
            return Err(VMError::InvalidHead {
                error_description: "can't exceed rightmost position",
                bad_instruction: i,
            });
        }
        self.data_head += 1;
        Ok(())
    }
    /// Increment value at a particular position, returning an error if value is too high
    pub fn increment_value(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        let new_value = self.tape[self.data_head].inc_value();
        // If returns error, then test
        match new_value {
            Err(_e) => {
                println!("FAILED");
                return Err(VMError::InvalidData {
                    error_description: "Value too large for data type",
                    bad_instruction: i,
                });
            }
            Ok(ans) => {
                self.tape[self.data_head] = ans;
            }
        }
        Ok(())
    }
    /// Decrement value at particular position, returning an error if less than zero
    pub fn decrement_value(&mut self, i: &'a InputInstruction) -> Result<(), VMError> {
        let new_value = self.tape[self.data_head].sub_value();
        match new_value {
            Err(_e) => {
                return Err(VMError::InvalidData {
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
    /// Read byte from reader into data head's cell (ie "," command)
    pub fn read_byte(
        &mut self,
        i: &'a InputInstruction,
        reader: &mut dyn Read,
    ) -> Result<(), VMError> {
        let mut buff = [0; 1];
        match reader.read_exact(&mut buff) {
            Ok(()) => {
                // convert buffer byte (u8) to generic type
                self.tape[self.data_head] = buff[0].into();
                Ok(())
            }
            Err(_e) => {
                // println!("IO ERROR");
                Err(VMError::IOError {
                    error_desciption: "Error reading data byte",
                    bad_instruction: i,
                })
            }
        }
    }
    /// Output data byte
    pub fn out_byte(
        &mut self,
        i: &'a InputInstruction,
        writer: &mut dyn Write,
    ) -> Result<(), VMError> {
        // Stores first byte of cell's value
        // But needs to be as large as largest number type, for conversion
        let mut buff = [0; 1];
        buff[0] = self.tape[self.data_head].first_byte();
        // Write first byte to writer
        if let Err(_e) = writer.write(&buff) {
            return Err(VMError::IOError {
                error_desciption: "Error reading data byte",
                bad_instruction: i,
            });
        };
        Ok(())
    }
}

#[cfg(test)]

mod tests {

    use super::VMError;
    use bft_types::{InputInstruction, RawInstruction};

    use crate::BFProgram;
    //use crate::FirstByte;
    use crate::VM;
    use std::io::Cursor;

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
                error_description: "can't be below zero",
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
                error_description: "can't exceed rightmost position",
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
    /// Tape of u8 type.
    /// Increase value of cell to beyond u8's max size
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
            Err(VMError::InvalidData {
                error_description: "Value too large for data type",
                bad_instruction: i
            })
        );
    }

    #[test]
    /// Tape of u8 type.
    /// Try setting value of cell to less than zero
    fn data_dec_fail_low() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u8, &str> = VM::new(&p, 5, false);
        assert_eq!(vm.data_head(), 0);
        assert_eq!(vm.tape[vm.data_head], 0);
        // Try to decrease below zero
        let ans = vm.decrement_value(i);
        assert_eq!(
            ans,
            Err(VMError::InvalidData {
                error_description: "Value cannot be smaller than zero",
                bad_instruction: i
            })
        );
    }
    // Test read_byte
    // Create VM with 2 cells, u8 type
    // Initialise a reader using Cursor trait (why?)
    // Read one byte into first cell
    // Check first cell contains new byte, second unchanged

    #[test]
    /// Test read_byte from spoofed reader.
    /// Check works when VM's data type is *not u8.
    fn read_byte_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u16, &str> = VM::new(&p, 5, false);
        // non-shared bit
        let mut spoofed_reader: Cursor<Vec<u8>> = Cursor::new(vec![11, 12, 13]);
        vm.read_byte(i, &mut spoofed_reader).unwrap();
        // Reader should be unchanged
        assert_eq!(spoofed_reader.into_inner(), vec![11, 12, 13]);
        // Tape's first bit should be changed
        assert_eq!(*vm.tape(), vec![11, 0, 0, 0, 0]);
    }

    #[test]
    /// Test outputting data byte into spoofed writer.
    /// Check works when VM's data type is *not* u8.
    fn out_byte_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let i = &InputInstruction::new(RawInstruction::PointerDec, 2, 3);
        let mut vm: VM<u16, &str> = VM::new(&p, 5, false);
        // non-shared bit
        let mut spoofed_writer: Cursor<Vec<u8>> = Cursor::new(vec![11, 12, 13]);
        vm.out_byte(i, &mut spoofed_writer).unwrap();
        // Tape's first bit should be unchanged
        assert_eq!(*vm.tape(), vec![0, 0, 0, 0, 0]);
        // Writer's first bit should have changed
        assert_eq!(spoofed_writer.into_inner(), vec![0, 12, 13]);
    }

    // Test test input non-u8 data into u8 VM
}
