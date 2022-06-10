//! Useful types for BF interpreter.
//!
//!
//! Contains a struct for a BF program, and methods to read instructions from a file.
#![warn(missing_docs)]

use std::path::Path;
use std::{fmt, fs};
use thiserror::Error;

/// Enum for raw instructions, corresponding to the 8 input characters.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RawInstruction {
    /// Increment pointer
    PointerInc,
    /// Decrement pointer
    PointerDec,
    /// Increment data byte
    ByteInc,
    /// Decrement data byte
    ByteDec,
    /// Output data byte
    ByteOut,
    /// Accept data byte
    ByteAccept,
    /// If zero, jump forward
    JumpForward,
    /// If zero, jump backward
    JumpBack,
}

impl RawInstruction {
    /// Convert a char into a raw instruction.

    pub fn from_char(c: char) -> Option<RawInstruction> {
        match c {
            '>' => Some(Self::PointerInc),
            '<' => Some(Self::PointerDec),
            '+' => Some(Self::ByteInc),
            '-' => Some(Self::ByteDec),
            '.' => Some(Self::ByteOut),
            ',' => Some(Self::ByteAccept),
            '[' => Some(Self::JumpForward),
            ']' => Some(Self::JumpBack),
            _ => None,
        }
    }
}

impl fmt::Display for RawInstruction {
    /// Print interpretation of instruction.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RawInstruction::PointerDec => write!(f, "Decrement current location"),
            RawInstruction::PointerInc => write!(f, "Increment current location"),
            RawInstruction::ByteInc => write!(f, "Increment data"),
            RawInstruction::ByteDec => write!(f, "Decrement data"),
            RawInstruction::ByteAccept => write!(f, "Accept Data"),
            RawInstruction::ByteOut => write!(f, "Output Data"),
            RawInstruction::JumpForward => write!(f, "If zero jump forward to next ]"),
            RawInstruction::JumpBack => write!(f, "If non zero jump back to previous ["),
        }
    }
}

#[derive(Error, Debug, PartialEq)]
/// Enum for program errors
pub enum BFError {
    #[error("Bracket not closed. Type is {}", bad_bracket)]
    /// Bad bracket error type
    BracketError {
        /// Bad bracket: "[" or "]"
        bad_bracket: String,
        /// Line of bad bracket
        bad_line: usize,
        /// Col of bad bracket
        bad_col: usize,
    },
}

/// Represent an input instruction, inc. line and col numbers
#[derive(Debug)]
pub struct InputInstruction {
    instruction: RawInstruction,
    line_num: usize,
    col_num: usize,
}

impl InputInstruction {
    /// Create a new input instruction
    pub fn new(instruction: RawInstruction, line_num: usize, col_num: usize) -> Self {
        Self {
            instruction,
            line_num,
            col_num,
        }
    }
}

impl fmt::Display for InputInstruction {
    /// Display an input instruction in a helpful way.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{}:{}] {}",
            self.line_num, self.col_num, self.instruction
        )
    }
}

#[derive(Debug)]
/// Represent a BF program: file name and its associated instructions.
///
// Accepts a generic type: anything which can be implicitly converted to
// a reference to a path.
pub struct BFProgram<P: AsRef<Path>> {
    // Why do I get a warning here?
    file_name: P,
    instructions: Vec<InputInstruction>,
}

impl<P: AsRef<Path>> BFProgram<P> {
    /// Getter function for file name
    pub fn file_name(&self) -> &P {
        &self.file_name
    }

    /// Getter function for (private) instructions
    pub fn instructions(&self) -> &Vec<InputInstruction> {
        &self.instructions
    }

    /// Check brackets balanced.
    ///
    /// This method would easily generalise to an arbitrary number of bracket types
    pub fn check_brackets_balanced(&self) -> Result<(), BFError> {
        let mut stack: Vec<RawInstruction> = Vec::new();
        let mut line_last_open = 0;
        let mut col_last_open = 0;
        for i in self.instructions() {
            let raw = i.instruction;
            match raw {
                RawInstruction::JumpForward => {
                    // push raw instruction to vector
                    // Save last line and col of stack's top
                    stack.push(raw);
                    line_last_open = i.line_num;
                    col_last_open = i.col_num;
                }
                RawInstruction::JumpBack => {
                    // attempt to pop back
                    // if fail, return an error
                    stack.pop().ok_or(BFError::BracketError {
                        bad_bracket: "]".to_string(),
                        bad_line: i.line_num,
                        bad_col: i.col_num,
                    })?;
                }
                _ => {}
            }
        }
        // If any brackets remain, return an error
        if !stack.is_empty() {
            return Err(BFError::BracketError {
                bad_bracket: "[".to_string(),
                bad_line: line_last_open,
                bad_col: col_last_open,
            });
        }
        Ok(())
    }

    // implicitly converted into a ref to a path
    /// Create a new BF program from a file and its contents
    pub fn new(file_name: P, content: String) -> Self {
        let mut instructions = Vec::new();
        let mut line_count = 1;
        for line in content.lines() {
            let mut col_count = 1;
            for c in line.chars() {
                let instruction = RawInstruction::from_char(c);
                if let Some(i) = instruction {
                    // Nice alternative to "match" if only want to do
                    // something in affirmative case
                    instructions.push(InputInstruction::new(i, line_count, col_count));
                }
                col_count += 1;
            }
            line_count += 1;
        }
        Self {
            file_name,
            instructions,
        }
    }

    /// Read from a file and create a new BF program from its content
    /// # Examples
    // Some code (run as user, need to include crates):
    /// ```
    ///
    /// use bft_types::BFProgram;
    /// let prog = BFProgram::from_file("example_commands");
    /// ```
    pub fn from_file(file_name: P) -> Result<BFProgram<P>, Box<dyn std::error::Error>> {
        let f = file_name.as_ref();
        let content = fs::read_to_string(f)?;
        let prog = BFProgram::new(file_name, content);
        prog.check_brackets_balanced()?;
        Ok(prog)
    }
}

#[cfg(test)]
mod tests {
    use crate::BFError;
    //use crate::BFError;
    use crate::BFProgram;
    use crate::RawInstruction;

    #[test]
    fn run_print_instruction() {
        let prog = BFProgram::new("TestFile", "<>+-hello>\n,[chris].".to_string());
        // Test first instruction
        assert_eq!(prog.instructions[0].instruction, RawInstruction::PointerDec);
        // Test last instruction
        if let Some(last_input_instruction) = prog.instructions.last() {
            println!("{:?}", last_input_instruction.instruction);
            assert_eq!(last_input_instruction.instruction, RawInstruction::ByteOut);
        }
        // Test for correct number of instructions
        assert_eq!(prog.instructions.len(), 9);
        // Test that instruction 9 is in line 2, col 9
        assert_eq!(prog.instructions[8].line_num, 2);
        assert_eq!(prog.instructions[8].col_num, 9);
    }

    #[test]
    fn read_from_empty_file() {
        let prog = BFProgram::new("EmptyFile", "".to_string());
        // Test first instruction
        assert_eq!(prog.instructions.len(), 0);
    }

    #[test]
    /// Too many open brackets
    fn bracket_error_open() {
        let prog = BFProgram::new("TestFile", "[[[]".to_string());
        let result = prog.check_brackets_balanced();
        assert_eq!(
            result,
            Err(BFError::BracketError {
                bad_bracket: "[".to_string(),
                bad_col: 3,
                bad_line: 1,
            })
        );
    }

    /// Too few open brackets
    #[test]
    fn bracket_error_closed() {
        let prog = BFProgram::new("TestFile", "[][]\n]".to_string());
        let result = prog.check_brackets_balanced();
        assert_eq!(
            result,
            Err(BFError::BracketError {
                bad_bracket: "]".to_string(),
                bad_col: 1,
                bad_line: 2,
            })
        );
    }
}
