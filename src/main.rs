use anyhow::Result;
use clap::Parser;
use std::fs;
use tiger::{eval::eval, parser::parse, types::check};

/// Tiger language interpreter
#[derive(Parser, Debug)]
struct Args {
    /// Skip type check
    #[arg(short, long)]
    skip_type_check: bool,

    file_name: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let src = fs::read_to_string(args.file_name)?;
    let ast = parse(&src)?;
    if !args.skip_type_check {
        check(&ast)?;
    }
    eval(&ast)?;
    Ok(())
}
