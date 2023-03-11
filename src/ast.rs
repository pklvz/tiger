use std::fmt::Display;

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

pub struct Field {
    pub name: String,
    pub ty: String,
}

pub enum Type {
    Type(String),
    Array(String),
    Rec(Vec<Field>),
}

pub enum Dec {
    TyDec(String, Type),
    VarDec {
        name: String,
        ty: Option<String>,
        val: Box<Expr>,
    },
    FnDec {
        name: String,
        fields: Vec<Field>,
        retty: Option<String>,
        body: Box<Expr>,
    },
}

pub enum Lvalue {
    Var(String),
    Rec(Box<Lvalue>, String),
    Idx(Box<Lvalue>, Box<Expr>),
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

pub enum Expr {
    BinOp {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        op: Op,
    },
    Nil,
    Neg(Box<Expr>),
    Seq(Vec<Expr>),
    Integer(isize),
    String(String),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    While(Box<Expr>, Box<Expr>),
    For(String, Box<Expr>, Box<Expr>, Box<Expr>),
    Break,
    Let(Vec<Dec>, Box<Expr>),
    FnCall {
        name: String,
        args: Vec<Expr>,
    },
    Rec {
        ty: String,
        fields: Vec<(String, Expr)>,
    },
    Array {
        ty: String,
        n: Box<Expr>,
        v: Box<Expr>,
    },
    Assign(Lvalue, Box<Expr>),
    Lvalue(Lvalue),
}
