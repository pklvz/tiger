use anyhow::{anyhow, Result};
use clap::Parser;
use std::fs;
use tiger::{eval::eval, parser::parse, types::check};

/// Tiger language interpreter
#[derive(Parser, Debug)]
struct Args {
    /// Skip type check
    #[arg(short, long)]
    skip_type_check: bool,

    filename: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let src = fs::read_to_string(args.filename)?;
    let ast = parse(&src).map_err(|error| anyhow!("syntax error: {}", error))?;
    if !args.skip_type_check {
        check(&ast).map_err(|error| anyhow!("type error: {}", error))?;
    }
    eval(&ast).map_err(|error| anyhow!("runtime error: {}", error))?;
    Ok(())
}
