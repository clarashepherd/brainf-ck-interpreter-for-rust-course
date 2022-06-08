#![warn(missing_docs)]
use clap::Parser;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[clap(author, version, about)]

/// Command line interface for BF itnerpreter
pub struct Options {
    /// Name of file containing BF program
    pub file_name: PathBuf,
}
