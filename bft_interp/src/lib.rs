//! Contains structs and methods for BF interpreter.
//! Currently just prints instructions.
#![warn(missing_docs)]

use bft_types::RawInstruction;
use bft_types::{BFProgram, InputInstruction};
use std::clone;
use std::cmp;
use std::convert;
use std::io::{self, Read, Write};
use thiserror::Error;

/// TODO doc
pub struct ContainsWriter<W: Write> {
    /// TODO doc or make private
    pub writer: W,
    /// TODO doc or make private
    pub last_character_newline: bool,
}

impl<W> Write for ContainsWriter<W>
where
    W: Write,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        //println!("Got here");
        let ans = Write::write(&mut self.writer, buf);
        if let Ok(num_bytes) = ans {
            if buf[num_bytes - 1] == b'\n' {
                // last chracter was newline
                //println!("last char was newline");
                self.last_character_newline = true;
            } else {
                //println!("last char was not newline");
                self.last_character_newline = false;
            }
        }
        ans
    }
    fn flush(&mut self) -> io::Result<()> {
        Write::flush(&mut self.writer)
    }
}

impl<W> Drop for ContainsWriter<W>
where
    W: Write,
{
    fn drop(&mut self) {
        if !self.last_character_newline {
            // last character was not newline, add one
            if let Err(_e) = Write::write(&mut self.writer, &[b'\n']) {
                println!("An error occurred while trying to write final newline");
            }
        }
    }
}

/// Represents virtual machine: tape with some number of cells, each of some type.
/// Includes option to dynamically grow tape.
// TODO how to make this lifetime compatible with that of VM?
// I can't currently let VMError return a *reference* to an instruction
#[derive(Clone)]
pub struct VM<'a, T>
where
    // Satisfies base trait for numeric types, and clone
    T: CellKind,
{
    /// Borrow of program TOOD why
    prog: &'a BFProgram,
    /// Number of cells
    num_cells: usize,
    /// Location of data pointer's head
    data_pointer: usize,
    /// Location of instruction pointer (program counter)
    instruction_pointer: usize,
    /// Tape
    tape: Vec<T>,
    /// Is tape allowed to dynamically grow?
    is_auto_extending: bool,
}

#[derive(Error, Debug, cmp::PartialEq, Clone, Copy)]
/// Enum for VM errors
// Comment from Daniel: OK that bad_instruction isn't a reference:
// don't want errors to be borrows, because propagating them becomes a tangle.
// Also, expect them to be rare so overheads are quite low.
pub enum VMError {
    #[error(
        "Invalid head position: {}, bad instruction: {}",
        error_description,
        bad_instruction
    )]
    /// Bad bracket error type
    InvalidHead {
        /// Error description
        error_description: &'static str,
        /// Instruction causing error
        bad_instruction: InputInstruction,
    },
    #[error("I/O error, bad instruction: {}", bad_instruction)]
    /// I/O errors from reader/writer functionality
    IOError {
        /// Eror desscription
        error_desciption: &'static str,
        /// Instruction causing error
        bad_instruction: InputInstruction,
    },
    #[error("Can't find matching bracket, bad instruction {}", bad_instruction)]
    /// Bracket error not picked up by matching
    CantFindBracket {
        /// Error description
        error_description: &'static str,
        /// Instructin causing error
        bad_instruction: InputInstruction,
    },
}

/// CellKind trait
/// Implements additon and subtraction
/// If can't add/subtract any further, returns modulus
/// e.g. 255+1 = 0
pub trait CellKind {
    /// Increment value by one
    fn inc_value(&self) -> Self
    where
        Self: std::marker::Sized;
    /// Decrement value by one
    fn sub_value(&self) -> Self
    where
        Self: std::marker::Sized;
}

impl<T> CellKind for T
where
    T: num_traits::WrappingAdd + num_traits::WrappingSub + From<u8>,
{
    fn inc_value(&self) -> Self {
        self.wrapping_add(&T::from(1))
    }
    fn sub_value(&self) -> Self {
        self.wrapping_sub(&T::from(1))
    }
}
/////////////
// TODO
// Daniel: Is there a good reason this function isn't part of CellKind, rather than
// being an independent trait?
//
// Chris: I think so? I want the above impl to work for u8, u16, i16, ...
// To add the first_byte function, the generic T needs to implement to_be_bytes(&self) -> u8(*some_dynamic_size*).
// The problem is, the size of to_be_bytes output depends on the type, and AFAIK rust
// can't determine this dynamically.
// Any pointers here?
///////////
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
impl<'a, T> VM<'a, T>
where
    T: num_traits::Num
        + num_traits::Zero
        + clone::Clone
        + CellKind
        + std::default::Default
        + convert::From<u8>
        + FirstByte,
{
    /// Create new VM with some size, can choose whether to grow.
    /// If given size is zero, tape is 30,000 bytes long.
    pub fn new(prog: &'a BFProgram, size: usize, is_auto_extending: bool) -> Self {
        let mut num_cells = 30000;
        if size != 0 {
            num_cells = size;
        };
        let tape: Vec<T> = vec![Default::default(); num_cells];
        Self {
            prog,
            num_cells,
            tape,
            is_auto_extending,
            data_pointer: 0,
            instruction_pointer: 0,
        }
    }

    // Actions corresponding to input instructions.
    // All these functions return the next instruction pointer to use
    /// Move head left.
    fn move_head_left(&mut self) -> Result<usize, VMError> {
        if self.data_pointer == 0 {
            return Err(VMError::InvalidHead {
                error_description: "can't be below zero",
                bad_instruction: self.prog.instructions[self.instruction_pointer],
            });
        }
        self.data_pointer -= 1;
        Ok(self.instruction_pointer + 1)
    }
    /// Move head right
    pub fn move_head_right(&mut self) -> Result<usize, VMError> {
        if self.data_pointer == self.num_cells - 1 {
            if !self.is_auto_extending {
                return Err(VMError::InvalidHead {
                    error_description: "can't exceed rightmost position",
                    bad_instruction: self.prog.instructions[self.instruction_pointer],
                });
            } else {
                // extend the tape
                self.num_cells += 1;
                self.tape.push(T::from(0));
            }
        }
        self.data_pointer += 1;
        Ok(self.instruction_pointer + 1)
    }
    /// Increment value at a particular position, returning an error if value is too high
    fn increment_value(&mut self) -> Result<usize, VMError> {
        // Kind of bad naming here
        self.tape[self.data_pointer] = self.tape[self.data_pointer].inc_value();
        Ok(self.instruction_pointer + 1)
    }
    /// Decrement value at particular position, returning an error if less than zero
    fn decrement_value(&mut self) -> Result<usize, VMError> {
        self.tape[self.data_pointer] = self.tape[self.data_pointer].sub_value();
        Ok(self.instruction_pointer + 1)
    }
    /// Read byte from reader into data head's cell (ie "," command)
    fn read_byte(&mut self, reader: &mut dyn Read) -> Result<usize, VMError> {
        let mut buff = [0; 1];
        match reader.read_exact(&mut buff) {
            Ok(()) => {
                // convert buffer byte (u8) to generic type
                self.tape[self.data_pointer] = buff[0].into();
                Ok(self.instruction_pointer + 1)
            }
            Err(_e) => {
                // println!("IO ERROR");
                Err(VMError::IOError {
                    error_desciption: "Error reading data byte",
                    bad_instruction: self.prog.instructions[self.instruction_pointer],
                })
            }
        }
    }
    /// Output data byte
    fn out_byte(&mut self, writer: &mut dyn Write) -> Result<usize, VMError> {
        // Stores first byte of cell's value.
        // But needs to be as large as largest number type, for conversion.
        let mut buff = [0; 1];
        buff[0] = self.tape[self.data_pointer].first_byte();
        // Write first byte to writer
        if let Err(_e) = writer.write(&buff) {
            return Err(VMError::IOError {
                error_desciption: "Error reading data byte",
                bad_instruction: self.prog.instructions[self.instruction_pointer],
            });
        };
        Ok(self.instruction_pointer + 1)
    }
    /// Unconditionally jump program counter forward to matching "]" instruction.
    fn jump_forward(&mut self) -> Result<usize, VMError> {
        // Search beyond current instruction pointer for next instruction corresponding to "]".
        let pos_next_jump_back = &self
            .prog
            .instructions()
            .iter()
            .skip(self.instruction_pointer + 1)
            .position(|x| x.instruction() == RawInstruction::JumpBack);
        // Don't expect any errors here: should have caught in bracket matching.
        // Counting from position of instruction pointer
        match pos_next_jump_back {
            Some(pos) => Ok(pos + self.instruction_pointer + 1),
            None => Err(VMError::CantFindBracket {
                error_description: "Can't find matching ']' bracket",
                bad_instruction: self.prog.instructions[self.instruction_pointer],
            }),
        }
    }
    /// Conditionally jump program counter forward to matching "[" instruction.
    /// Condition: byte at data pointer *not* zero.
    fn jump_back(&mut self) -> Result<usize, VMError> {
        // Search beyond current instruction pointer for next instruction corresponding to "[".
        if !self.tape[self.data_pointer].is_zero() {
            let num_instructions = self.prog.instructions().len();
            let skip_from_rhs = num_instructions - self.instruction_pointer;
            //println!("JUMP BACK: skip_from_rhs = {}", skip_from_rhs);
            let pos_next_jump_forward = self
                .prog
                .instructions()
                .iter()
                .rev()
                .skip(skip_from_rhs)
                .position(|x| x.instruction() == RawInstruction::JumpForward);
            // Don't expect any errors here: should have caught in bracket matching.
            match pos_next_jump_forward {
                Some(pos) => {
                    //println!("Number of extra RHS iterations: {}", pos);
                    // Position of matching "[" *plus one*
                    Ok(self.instruction_pointer - pos)
                }
                None => Err(VMError::CantFindBracket {
                    error_description: "Can't find matching '[' bracket",
                    bad_instruction: self.prog.instructions[self.instruction_pointer],
                }),
            }
        } else {
            Ok(self.instruction_pointer + 1)
        }
    }
    /// Interpret the instructions at some given path.
    /// Currently just prints their content.
    pub fn interpret<R, W>(&mut self, input: &mut R, output: &mut W) -> Result<(), VMError>
    where
        R: Read,
        W: Write,
    {
        while self.instruction_pointer < self.prog.instructions.len() {
            let i = self.prog.instructions[self.instruction_pointer];
            let ans: Result<usize, VMError>;
            match i.instruction() {
                RawInstruction::PointerInc => ans = self.move_head_right(),
                RawInstruction::PointerDec => ans = self.move_head_left(),
                RawInstruction::ByteInc => ans = self.increment_value(),
                RawInstruction::ByteDec => ans = self.decrement_value(),
                RawInstruction::ReadByte => ans = self.read_byte(input),
                RawInstruction::OutByte => ans = self.out_byte(output),
                RawInstruction::JumpForward => ans = self.jump_forward(),
                RawInstruction::JumpBack => ans = self.jump_back(),
            }
            self.instruction_pointer = ans?;
        }
        Ok(())
    }
}

#[cfg(test)]

mod tests {

    use super::VMError;

    use crate::BFProgram;
    use crate::ContainsWriter;
    use crate::VM;
    use crate::{CellKind, FirstByte};
    use assert_fs::prelude::*;
    use std::io::{Cursor, Write};

    // Useful function
    impl<'a, T> VM<'a, T>
    where
        T: num_traits::Num
            + num_traits::Zero
            + std::clone::Clone
            + CellKind
            + std::default::Default
            + std::convert::From<u8>
            + FirstByte,
    {
        /// Get value at data head
        fn head_value(&mut self) -> T {
            self.tape[self.data_pointer].clone()
        }
    }

    #[test]
    /// Check for failure when pointer goes too far left
    fn pointer_left_fail() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u8> = VM::new(&p, 0, false);
        assert_eq!(vm.data_pointer, 0);
        let ans = vm.move_head_left();
        assert_eq!(
            ans,
            Err(VMError::InvalidHead {
                error_description: "can't be below zero",
                bad_instruction: vm.prog.instructions[vm.instruction_pointer],
            })
        );
    }

    #[test]
    /// Check for failure when pointer goes too far
    fn pointer_right_fail() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u8> = VM::new(&p, 0, false);
        assert_eq!(vm.data_pointer, 0);
        let mut _ans;
        for _n in 0..vm.num_cells - 1 {
            _ans = vm.move_head_right();
        }
        let ans = vm.move_head_right();
        assert_eq!(
            ans,
            Err(VMError::InvalidHead {
                error_description: "can't exceed rightmost position",
                bad_instruction: vm.prog.instructions[vm.instruction_pointer]
            })
        );
    }

    #[test]
    fn pointer_right_left_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u8> = VM::new(&p, 0, false);
        assert_eq!(vm.data_pointer, 0);
        let mut _ans;
        for _n in 0..10 {
            _ans = vm.move_head_right();
        }
        assert_eq!(vm.data_pointer, 10);
        for _n in 0..5 {
            _ans = vm.move_head_left();
        }
        assert_eq!(vm.data_pointer, 5);
    }

    #[test]
    fn move_pointer_tape_grows_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u8> = VM::new(&p, 1, true);
        assert_eq!(vm.data_pointer, 0);
        // Create one extra cell
        let _ans = vm.move_head_right();
        // Check cell exists and is empty
        assert_eq!(vm.num_cells, 2);
        assert_eq!(vm.tape[1], 0);
    }

    #[test]
    /// Tape of u8 type.
    /// Increase value of cell to beyond u8's max size
    fn data_inc_dec_ok_wrap_high() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u8> = VM::new(&p, 0, false);
        assert_eq!(vm.data_pointer, 0);
        assert_eq!(vm.tape[vm.data_pointer], 0);
        // Increase to max size
        for _n in 0..255 {
            let _ans = vm.increment_value();
        }
        assert_eq!(vm.head_value(), 255);
        // Decrease by one
        let _ans = vm.decrement_value();
        assert_eq!(vm.head_value(), 254);
        // Increase by one
        let _ans = vm.increment_value();
        assert_eq!(vm.head_value(), 255);
        // Increase past max size
        let _ans = vm.increment_value();
        assert_eq!(vm.head_value(), 0);
    }

    #[test]
    /// Tape of u8 type.
    /// Try setting value of cell to less than zero
    fn data_dec_wrap_low() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u8> = VM::new(&p, 5, false);
        assert_eq!(vm.data_pointer, 0);
        assert_eq!(vm.tape[vm.data_pointer], 0);
        // Try to decrease below zero
        let _ans = vm.decrement_value();
        assert_eq!(vm.head_value(), u8::MAX);
    }

    #[test]
    /// Test read_byte from spoofed reader.
    /// Check works when VM's data type is *not u8.
    fn read_byte_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u16> = VM::new(&p, 5, false);
        // non-shared bit
        let mut spoofed_reader: Cursor<Vec<u8>> = Cursor::new(vec![11, 12, 13]);
        vm.read_byte(&mut spoofed_reader).unwrap();
        // Reader should be unchanged
        assert_eq!(spoofed_reader.into_inner(), vec![11, 12, 13]);
        // Tape's first bit should be changed
        assert_eq!(*vm.tape, vec![11, 0, 0, 0, 0]);
    }

    #[test]
    /// Test outputting data byte into spoofed writer.
    /// Check works when VM's data type is *not* u8.
    fn out_byte_ok() {
        let p = BFProgram::new("TestFile", "<>.hello.".to_string());
        let mut vm: VM<u16> = VM::new(&p, 5, false);
        // non-shared bit
        let mut spoofed_writer: Cursor<Vec<u8>> = Cursor::new(vec![11, 12, 13]);
        vm.out_byte(&mut spoofed_writer).unwrap();
        // Tape's first bit should be unchanged
        assert_eq!(*vm.tape, vec![0, 0, 0, 0, 0]);
        // Writer's first bit should have changed
        assert_eq!(spoofed_writer.into_inner(), vec![0, 12, 13]);
    }

    #[test]
    /// Test unconditonal jump to "]"
    fn jump_forward_ok_fail() {
        let p = BFProgram::new("TestFile", "ab.[<>cd]..".to_string());
        let mut vm: VM<u16> = VM::new(&p, 5, false);
        // Spoof position of first "[".
        // Note: only valid instructions are counted, so the first "[" is at position 1, "]" at position 4.
        // Correctly find "]" position.
        vm.instruction_pointer = 1;
        let mut ans = vm.jump_forward();
        assert_eq!(ans, Ok(4));
        // Return an error when can't find matching bracket.
        vm.instruction_pointer = 4;
        ans = vm.jump_forward();
        assert_eq!(
            ans,
            Err(VMError::CantFindBracket {
                error_description: "Can't find matching ']' bracket",
                bad_instruction: vm.prog.instructions[vm.instruction_pointer]
            })
        );
    }
    #[test]
    /// Test conditional jump to "]"
    fn jump_back_ok_fail() {
        let p = BFProgram::new("TestFile", "ab.[<>cd]..".to_string());
        let mut vm: VM<u16> = VM::new(&p, 5, false);
        /////////////////////
        // Nonzero data bit, do jumps
        //
        // Spoof position of first "]".
        // Correctly find "[" position"]
        vm.tape[vm.data_pointer] = 100;
        vm.instruction_pointer = 4;
        let mut ans = vm.jump_back();
        assert_eq!(ans, Ok(2));
        // Return an error when can't find matching bracket
        vm.instruction_pointer = 1;
        ans = vm.jump_back();
        assert_eq!(
            ans,
            Err(VMError::CantFindBracket {
                error_description: "Can't find matching '[' bracket",
                bad_instruction: vm.prog.instructions[vm.instruction_pointer]
            })
        );
        ////////////////////
        // Zero data bit, don't jump
        vm.tape[vm.data_pointer] = 0;
        vm.instruction_pointer = 4;
        ans = vm.jump_back();
        assert_eq!(ans, Ok(5));
    }

    #[test]

    // Check counting ok for backwards searching
    fn jump_back_catch_all() {
        let p = BFProgram::new("TestFile", "[[[[[[[[[[[".to_string());
        let mut vm: VM<u16> = VM::new(&p, 5, false);
        /////////////////////
        // Nonzero data bit, do jumps
        //
        vm.instruction_pointer = 4;
        // Correctly move instruction pointer one to the left
        vm.tape[vm.data_pointer] = 100;
        let ans = vm.jump_back();
        assert_eq!(ans, Ok(4));
    }

    #[test]
    /// Check that interpret function correctly gives hello_world message,
    /// TODO only operator not tested is ","
    fn test_hello_world() -> Result<(), Box<dyn std::error::Error>> {
        // Spoof file, reader, writer
        let temp_file = assert_fs::NamedTempFile::new("helloWorld.txt")?;
        temp_file.write_str(
            ">++++++++[<+++++++++>-]<.>++++[<+++++++>-]<+.+++++++..+++.>>++++++[<+++++++>-]<+
        +.------------.>++++++[<+++++++++>-]<+.<.+++.------.--------.>>>++++[<++++++++>-
        ]<+.",
        )?;
        let mut spoofed_reader: Cursor<Vec<u8>> = Cursor::new(vec![0; 20]);
        let mut spoofed_writer: Cursor<Vec<u8>> = Cursor::new(vec![0; 20]);
        // Read program and interpret
        let program = bft_types::BFProgram::from_file(temp_file.path()).unwrap();
        let mut vm: VM<u8> = VM::new(&program, 10, false);
        let _ans = vm.interpret(&mut spoofed_reader, &mut spoofed_writer);
        let message_bits: Vec<u8> = spoofed_writer
            .into_inner()
            .into_iter()
            .filter(|x| *x != 0)
            .collect();
        println!("{:?}", message_bits);
        let message = std::str::from_utf8(&message_bits).unwrap();
        assert_eq!(message, "Hello, World!");
        Ok(())
    }

    #[test]
    /// Check that interpret function correctly reads a data byte,
    fn test_read_byte() -> Result<(), Box<dyn std::error::Error>> {
        // Spoof file, reader, writer
        let temp_file = assert_fs::NamedTempFile::new("outputTwo.txt")?;
        temp_file.write_str(",")?;
        let mut spoofed_reader: Cursor<Vec<u8>> = Cursor::new(vec![10; 5]);
        let mut spoofed_writer: Cursor<Vec<u8>> = Cursor::new(vec![0; 5]);
        // Read program and interpret
        let program = bft_types::BFProgram::from_file(temp_file.path()).unwrap();
        let mut vm: VM<u8> = VM::new(&program, 5, false);
        let _ans = vm.interpret(&mut spoofed_reader, &mut spoofed_writer);
        assert_eq!(vm.tape, [10, 0, 0, 0, 0]);
        Ok(())
    }

    #[test]
    /// Check rapped writer, no newline added if there's one already
    fn reader_already_newline() -> Result<(), Box<dyn std::error::Error>> {
        let output = Cursor::new(vec![0; 5]);
        let mut wrapped = ContainsWriter {
            writer: output,
            last_character_newline: false,
        };
        wrapped.write(&[1, 2, b'\n']).ok();
        wrapped.flush()?;
        let mut rhs = Cursor::new(vec![1, 2, b'\n', 0, 0]);
        rhs.set_position(3);
        assert_eq!(wrapped.writer, rhs);
        Ok(())
    }
    /* TODO can't test drop here w/o stdout shenanigans
    // Already tested that way in tests/cli.rs
    // Any suggestions for how I could also test here, or should I drop it?
    #[test]
    /// Check wrapped writer, no newline added if there's one already
    fn reader_needs_newline() -> Result<(), Box<dyn std::error::Error>> {
        let output = Cursor::new(vec![0; 5]);
        let mut wrapped = ContainsWriter {
            writer: output,
            last_character_newline: false,
        };
        wrapped.write(&[1, 2, b'\n']).ok();
        // extra write, not newline
        wrapped.write(&[4]).ok();
        wrapped.flush()?;
        drop(wrapped);
        let mut rhs = Cursor::new(vec![1, 2, b'\n', 4, b'\n']);
        rhs.set_position(5);
        assert_eq!(wrapped.writer, rhs);
        Ok(())
    }*/
}
