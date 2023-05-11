use crate::{
    ast::{Op, Pos, WithPos},
    parser::Rule,
};
use std::{io, num};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("{0}")]
    ParseError(pest::error::Error<Rule>),
    #[error("{}, {}", .0.pos, .0.inner)]
    ParseIntError(WithPos<num::ParseIntError>),

    #[error("{}, unsupported operand type(s) {lty} and {rty} for {}", .op.pos, .op.inner)]
    UnsupportedOperandType {
        op: WithPos<Op>,
        lty: String,
        rty: String,
    },
    #[error("{}, type mismatch, expected {expected}, found {}", .found.pos, .found.inner)]
    MismatchedTypes {
        expected: String,
        found: WithPos<String>,
    },
    #[error("{}, {} takes {expected} argument(s) but {found} were given", .name.pos, .name.inner)]
    MismatchedArgumentNum {
        name: WithPos<String>,
        expected: usize,
        found: usize,
    },
    #[error("{}, recursive type {}", .0.pos, .0.inner)]
    RecursiveType(WithPos<String>),
    #[error("{}, unknown type of {}", .0.pos, .0.inner)]
    UnknownType(WithPos<String>),
    #[error("{}, name {} is not defined", .0.pos, .0.inner)]
    NotDefined(WithPos<String>),
    #[error("{}, {} is not callable", .0.pos, .0.inner)]
    NotCallable(WithPos<String>),
    #[error("{}, {} is not record", .0.pos, .0.inner)]
    NotRecord(WithPos<String>),
    #[error("{}, record has no field {}", .0.pos, .0.inner)]
    NoSuchField(WithPos<String>),
    #[error("{}, {} is not array", .0.pos, .0.inner)]
    NotArray(WithPos<String>),
    #[error("{0}, break outside loop")]
    BreakOutsideLoop(Pos),

    #[error("{}, nil struct dereference", .0)]
    DerefNilStruct(Pos),
    #[error("{}, nil array dereference", .0)]
    DerefNilArray(Pos),
    #[error("{}, negative index {}", .0.pos, .0.inner)]
    NegtiveIndex(WithPos<isize>),
    #[error("{}, index {} out of range", .0.pos, .0.inner)]
    IndexOutOfRange(WithPos<usize>),
    #[error("{}, {}", .0.pos, .0.inner)]
    IOError(WithPos<io::Error>),
    #[error("{}, {}", .0.pos, .0.inner)]
    TryFromIntError(WithPos<num::TryFromIntError>),
    #[error("")]
    Break,
}
