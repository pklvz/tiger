use crate::parser::{parse_expr, parse_lvalue, Rule};
use anyhow::Error;
use pest::iterators::Pair;
use std::{fmt::Display, ops::Deref};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Gt,
    Ge,
    Lt,
    Le,
    Ne,
    Eq,
    And,
    Or,
}

impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "'+'"),
            Self::Sub => write!(f, "'-'"),
            Self::Mul => write!(f, "'*'"),
            Self::Div => write!(f, "'/'"),
            Self::Gt => write!(f, "'>'"),
            Self::Ge => write!(f, "'>='"),
            Self::Lt => write!(f, "'<'"),
            Self::Le => write!(f, "'<='"),
            Self::Ne => write!(f, "'!='"),
            Self::Eq => write!(f, "'='"),
            Self::And => write!(f, "'&'"),
            Self::Or => write!(f, "'|'"),
        }
    }
}

impl Op {
    pub(crate) fn with_pos(self, pair: Pair<Rule>) -> WithPos<Self> {
        WithPos {
            pos: pair.line_col().into(),
            inner: self,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub name: String,
    pub ty: WithPos<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Type(WithPos<String>),
    Array(WithPos<String>),
    Rec(Vec<Field>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Dec {
    TyDec(String, WithPos<Type>),
    VarDec {
        name: WithPos<String>,
        ty: Option<WithPos<String>>,
        val: Box<WithPos<Expr>>,
    },
    FnDec {
        name: String,
        fields: Vec<Field>,
        retty: Option<WithPos<String>>,
        body: Box<WithPos<Expr>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lvalue {
    Var(WithPos<String>),
    Rec(Box<Self>, WithPos<String>),
    Idx(Box<Self>, Box<WithPos<Expr>>),
}

impl Display for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lvalue::Var(var) => f.write_str(var),
            Lvalue::Rec(lvalue, field) => {
                lvalue.fmt(f)?;
                f.write_str(".")?;
                f.write_str(field)
            }
            Lvalue::Idx(lvalue, _) => {
                lvalue.fmt(f)?;
                f.write_str("[..]")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    BinOp {
        lhs: Box<Self>,
        rhs: Box<Self>,
        op: WithPos<Op>,
    },
    Nil,
    Neg(Box<WithPos<Self>>),
    Seq(Vec<Self>),
    Integer(isize),
    String(String),
    If(
        Box<WithPos<Self>>,
        Box<WithPos<Self>>,
        Option<Box<WithPos<Self>>>,
    ),
    While(Box<WithPos<Self>>, Box<WithPos<Self>>),
    For(String, Box<WithPos<Self>>, Box<WithPos<Self>>, Box<Self>),
    Break(WithPos<()>),
    Let(Vec<Dec>, Box<Self>),
    FnCall {
        name: WithPos<String>,
        args: Vec<WithPos<Self>>,
    },
    Rec {
        ty: WithPos<String>,
        fields: Vec<(WithPos<String>, WithPos<Self>)>,
    },
    Array {
        ty: WithPos<String>,
        n: Box<WithPos<Self>>,
        v: Box<WithPos<Self>>,
    },
    Assign(WithPos<Lvalue>, Box<WithPos<Self>>),
    Lvalue(WithPos<Lvalue>),
}

#[derive(Debug, Clone, Copy)]
pub struct Pos(usize, usize);

impl From<(usize, usize)> for Pos {
    fn from(value: (usize, usize)) -> Self {
        Self(value.0, value.1)
    }
}

impl Display for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.0, self.1 + 1)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct WithPos<T> {
    pub pos: Pos,
    pub inner: T,
}

impl<T> WithPos<T> {
    pub fn with_inner<P>(&self, inner: P) -> WithPos<P> {
        WithPos {
            pos: self.pos,
            inner,
        }
    }
}

impl<T> Deref for WithPos<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: PartialEq> PartialEq for WithPos<T> {
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }

    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl From<Pair<'_, Rule>> for WithPos<String> {
    fn from(value: Pair<Rule>) -> Self {
        WithPos {
            pos: value.line_col().into(),
            inner: value.as_str().into(),
        }
    }
}

impl TryFrom<Pair<'_, Rule>> for WithPos<Expr> {
    type Error = Error;

    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        Ok(WithPos {
            pos: value.line_col().into(),
            inner: parse_expr(value.into_inner())?,
        })
    }
}

impl TryFrom<Pair<'_, Rule>> for WithPos<Lvalue> {
    type Error = Error;

    fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
        Ok(WithPos {
            pos: value.line_col().into(),
            inner: parse_lvalue(value)?,
        })
    }
}

impl TryFrom<Pair<'_, Rule>> for Box<WithPos<Expr>> {
    type Error = Error;

    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        Ok(Box::new(value.try_into()?))
    }
}
