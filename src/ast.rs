use crate::{
    error::Error,
    parser::{parse_expr, parse_lvalue, Rule},
};
use pest::iterators::Pair;
use std::{
    borrow::{Borrow, Cow},
    fmt::Display,
    ops::Deref,
    rc::Rc,
};

#[derive(Debug, Clone, Copy)]
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
        write!(f, "'")?;
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Ne => write!(f, "!="),
            Self::Eq => write!(f, "="),
            Self::And => write!(f, "&"),
            Self::Or => write!(f, "|"),
        }?;
        write!(f, "'")
    }
}

#[derive(Debug, Clone)]
pub struct Field<'a> {
    pub name: &'a str,
    pub ty: WithPos<&'a str>,
}

#[derive(Debug, Clone)]
pub enum Type<'a> {
    Type(WithPos<&'a str>),
    Array(WithPos<&'a str>),
    Rec(Vec<Field<'a>>),
}

#[derive(Debug, Clone)]
pub enum Dec<'a> {
    TyDec {
        name: &'a str,
        ty: WithPos<Type<'a>>,
    },
    VarDec {
        name: WithPos<&'a str>,
        ty: Option<WithPos<&'a str>>,
        expr: Box<WithPos<Expr<'a>>>,
    },
    FunDec {
        name: &'a str,
        fields: Vec<Field<'a>>,
        retty: Option<WithPos<&'a str>>,
        body: Rc<WithPos<Expr<'a>>>,
    },
}

#[derive(Debug, Clone)]
pub enum Lvalue<'a> {
    Var(WithPos<&'a str>),
    Rec(Box<WithPos<Self>>, WithPos<&'a str>),
    Idx(Box<WithPos<Self>>, Box<WithPos<Expr<'a>>>),
}

impl<'a> Display for Lvalue<'a> {
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

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    BinOp {
        lhs: Box<Self>,
        rhs: Box<Self>,
        op: WithPos<Op>,
    },
    Nil,
    Neg(Box<WithPos<Self>>),
    Seq(Vec<Self>),
    Integer(isize),
    String(Cow<'a, str>),
    If(
        Box<WithPos<Self>>,
        Box<WithPos<Self>>,
        Option<Box<WithPos<Self>>>,
    ),
    While(Box<WithPos<Self>>, Box<WithPos<Self>>),
    For(&'a str, Box<WithPos<Self>>, Box<WithPos<Self>>, Box<Self>),
    Break(Pos),
    Let(Vec<Dec<'a>>, Box<Self>),
    FunCall {
        name: WithPos<&'a str>,
        args: Vec<WithPos<Self>>,
    },
    Rec {
        ty: WithPos<&'a str>,
        fields: Vec<(WithPos<&'a str>, WithPos<Self>)>,
    },
    Array {
        ty: WithPos<&'a str>,
        n: Box<WithPos<Self>>,
        v: Box<WithPos<Self>>,
    },
    Assign(WithPos<Lvalue<'a>>, Box<WithPos<Self>>),
    Lvalue(WithPos<Lvalue<'a>>),
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

impl<T> From<&WithPos<T>> for WithPos<String>
where
    T: Borrow<str>,
{
    fn from(value: &WithPos<T>) -> Self {
        WithPos {
            pos: value.pos,
            inner: value.inner.borrow().into(),
        }
    }
}

impl<'a> From<Pair<'a, Rule>> for WithPos<&'a str> {
    fn from(value: Pair<'a, Rule>) -> Self {
        WithPos {
            pos: value.line_col().into(),
            inner: value.as_str(),
        }
    }
}

impl<'a> TryFrom<Pair<'a, Rule>> for WithPos<Expr<'a>> {
    type Error = Error;

    fn try_from(value: Pair<'a, Rule>) -> Result<Self, Self::Error> {
        Ok(WithPos {
            pos: value.line_col().into(),
            inner: parse_expr(value)?,
        })
    }
}

impl<'a> TryFrom<Pair<'a, Rule>> for WithPos<Lvalue<'a>> {
    type Error = Error;

    fn try_from(value: Pair<'a, Rule>) -> Result<Self, Self::Error> {
        Ok(WithPos {
            pos: value.line_col().into(),
            inner: parse_lvalue(value)?,
        })
    }
}

impl<'a> TryFrom<Pair<'a, Rule>> for Box<WithPos<Expr<'a>>> {
    type Error = Error;

    fn try_from(value: Pair<'a, Rule>) -> Result<Self, Self::Error> {
        Ok(Box::new(value.try_into()?))
    }
}
