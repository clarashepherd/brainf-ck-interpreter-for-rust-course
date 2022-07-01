//! Useful types for BF interpreter.
//!
//!
//! Contains a struct for a BF program, and methods to read instructions from a file.
// TODO ask about:
// * conventions for 'use':
//   * combine as much as possible?
//   * include as little as possible?
//   * avoid 'use' entire trait name?
#![warn(missing_docs)]

use std::path::{Path, PathBuf};
use std::{fmt, fs};
use thiserror::Error;

/// Enum for raw instructions, corresponding to the 8 input characters.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RawInstruction {
    /// Increment data pointer
    PointerInc,
    /// Decrement data pointer
    PointerDec,
    /// Increment byte at data pointer's cell
    ByteInc,
    /// Decrement byte at data pointer's cell
    ByteDec,
    /// Output one byte of data from data pointer's cell
    OutByte,
    /// Read one byte into data pointer's cell
    ReadByte,
    /// If byte at data pointer is zero, jump instruction pointer forawrd to matching "]"
    JumpForward,
    /// If byte at data pointer is nonzero, jump instruction pointer back to matching "["
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
            '.' => Some(Self::OutByte),
            ',' => Some(Self::ReadByte),
            '[' => Some(Self::JumpForward),
            ']' => Some(Self::JumpBack),
            _ => None,
        }
    }
}

impl fmt::Display for RawInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RawInstruction::PointerDec => write!(f, "Decrement data pointer"),
            RawInstruction::PointerInc => write!(f, "Increment data pointer"),
            RawInstruction::ByteInc => write!(f, "Increment byte at data pointer's cell"),
            RawInstruction::ByteDec => write!(f, "Decrement byte at data pointer's cell"),
            RawInstruction::ReadByte => write!(f, " Read one byte into data pointer's cell"),
            RawInstruction::OutByte => {
                write!(f, "Output one byte of data from data pointer's cell")
            }
            RawInstruction::JumpForward => write!(
                f,
                "If byte at data pointer is zero, jump instruction pointer forawrd to matching ']'"
            ),
            RawInstruction::JumpBack => write!(
                f,
                "If byte at data pointer is nonzero, jump instruction pointer back to matching '['"
            ),
        }
    }
}

#[derive(Error, Debug, PartialEq)]
/// Enum for program errors
pub enum BFError {
    #[error(
        "Bracket not closed. Type is {}, line {}, col {}",
        bad_bracket,
        bad_line,
        bad_col
    )]
    /// Bad bracket error type
    BracketError {
        /// Bad bracket: "[" or "]"
        bad_bracket: char,
        /// Line of bad bracket
        bad_line: usize,
        /// Col of bad bracket
        bad_col: usize,
    },
}

/// Represent an input instruction, inc. line and col numbers
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct InputInstruction {
    instruction: RawInstruction,
    line_num: usize,
    col_num: usize,
}

impl InputInstruction {
    /// Getter function for input instruction
    pub fn instruction(&self) -> RawInstruction {
        self.instruction
    }
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
pub struct BFProgram {
    file_name: PathBuf,
    /// Program's instructions.
    pub instructions: Vec<InputInstruction>,
}

impl BFProgram {
    /// Getter for file name, only to shut clippy up
    /// TODO what can I change to not need this?
    pub fn file_name(&self) -> &PathBuf {
        &self.file_name
    }
    /// Getter function for (private) instructions
    pub fn instructions(&self) -> &[InputInstruction] {
        &self.instructions
    }

    /// Check brackets balanced.
    ///
    /// This method would easily generalise to an arbitrary number of bracket types
    fn check_brackets_balanced(&self) -> Result<(), BFError> {
        let mut stack: Vec<RawInstruction> = Vec::new();
        let mut line_last_open = 0;
        let mut col_last_open = 0;
        for i in &self.instructions {
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
                        bad_bracket: ']',
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
                bad_bracket: '[',
                bad_line: line_last_open,
                bad_col: col_last_open,
            });
        }
        Ok(())
    }

    // implicitly converted into a ref to a path
    /// Create a new BF program from a file and its contents
    pub fn new<P: AsRef<Path>>(
        file_name: P,
        content: String,
    ) -> Result<Self, Box<dyn std::error::Error>> {
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
        let prog = Self {
            file_name: file_name.as_ref().to_path_buf(),
            instructions,
        };
        prog.check_brackets_balanced()?;
        Ok(prog)
    }

    /// Read from a file and create a new BF program from its content
    /// # Examples
    // Some code (run as user, need to include crates):
    /// ```
    ///
    /// use bft_types::BFProgram;
    /// let prog = BFProgram::from_file("example_commands");
    /// ```
    pub fn from_file<P: AsRef<Path>>(
        file_name: P,
    ) -> Result<BFProgram, Box<dyn std::error::Error>> {
        let f = file_name.as_ref();
        let content = fs::read_to_string(f)?;
        let prog = BFProgram::new(file_name, content)?;
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
        let prog = BFProgram::new("TestFile", "<>+-hello>\n,[chris].".to_string()).unwrap();
        // Test first instruction
        assert_eq!(prog.instructions[0].instruction, RawInstruction::PointerDec);
        // Test last instruction
        if let Some(last_input_instruction) = prog.instructions.last() {
            // println!("{:?}", last_input_instruction.instruction);
            assert_eq!(last_input_instruction.instruction, RawInstruction::OutByte);
        }
        // Test for correct number of instructions
        assert_eq!(prog.instructions.len(), 9);
        // Test that instruction 9 is in line 2, col 9
        assert_eq!(prog.instructions[8].line_num, 2);
        assert_eq!(prog.instructions[8].col_num, 9);
    }

    #[test]
    fn read_from_empty_file() {
        let prog = BFProgram::new("EmptyFile", "".to_string()).unwrap();
        // Test first instruction
        assert_eq!(prog.instructions.len(), 0);
    }

    #[test]
    /// Too many open brackets
    fn bracket_error_open() {
        let prog = BFProgram::new("TestFile", "[[[]".to_string());
        if let Err(e) = prog {
            assert_eq!(
                *e.downcast::<BFError>().unwrap(),
                BFError::BracketError {
                    bad_bracket: '[',
                    bad_col: 3,
                    bad_line: 1,
                }
            );
        }
    }

    /// Too few open brackets
    #[test]
    fn bracket_error_closed() {
        let prog = BFProgram::new("TestFile", "[][]\n]".to_string());
        if let Err(e) = prog {
            assert_eq!(
                *e.downcast::<BFError>().unwrap(),
                BFError::BracketError {
                    bad_bracket: ']',
                    bad_col: 1,
                    bad_line: 2,
                }
            );
        }
    }
}
