#![warn(missing_docs)]
use clap::Parser;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[clap(author, version, about)]

/// Command line interface for BF itnerpreter
pub struct Args {
    /// Name of file containing BF program
    pub file_name: PathBuf,
    // Size of tape
    #[clap(short, long, default_value = "0")]
    pub num_cells: String,
    #[clap(short, long, default_value = "n")]
    pub extend_auto: String,
}
