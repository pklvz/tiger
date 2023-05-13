use anyhow::Result;
use clap::Parser;
use std::fs;
use tiger::{eval, parser, types};

/// Tiger language interpreter
#[derive(Parser, Debug)]
struct Args {
    file_name: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let src = fs::read_to_string(args.file_name)?;
    let ast = parser::parse(&src)?;
    types::check(&ast)?;
    eval::eval(&ast)?;
    Ok(())
}
