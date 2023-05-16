use crate::{
    ast::{Dec, Expr, Field, Lvalue, Op, Type, WithPos},
    error::Error,
};
use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use std::{borrow::Cow, collections::LinkedList};

#[derive(Parser)]
#[grammar = "tiger.pest"]
struct TigerParser;

fn apply(op: WithPos<Op>, exprs: &mut LinkedList<Expr>) {
    let rhs = exprs.pop_back().unwrap();
    let lhs = exprs.pop_back().unwrap();
    exprs.push_back(Expr::BinOp {
        lhs: lhs.into(),
        rhs: rhs.into(),
        op,
    });
}

fn priority(rule: Op) -> usize {
    match rule {
        Op::Mul | Op::Div => 4,
        Op::Add | Op::Sub => 3,
        Op::Gt | Op::Ge | Op::Lt | Op::Le | Op::Ne | Op::Eq => 2,
        Op::And => 1,
        Op::Or => 0,
    }
}

fn parse_fields(pair: Pair<Rule>) -> Vec<Field> {
    let mut pairs = pair.into_inner();
    let mut fields = Vec::new();
    while let Some(field) = pairs.next() {
        fields.push(Field {
            name: field.as_str(),
            ty: pairs.next().unwrap().into(),
        });
    }
    fields
}

pub(crate) fn parse_lvalue(pair: Pair<Rule>) -> Result<Lvalue, Error> {
    let pos = pair.line_col().into();
    let mut pairs = pair.into_inner();
    let mut lvalue = Lvalue::Var(pairs.next().unwrap().into());
    for suffix in pairs {
        let var = WithPos { inner: lvalue, pos }.into();
        lvalue = match suffix.as_rule() {
            Rule::lvaluefield => Lvalue::Rec(var, suffix.into_inner().next().unwrap().into()),
            Rule::lvalueidx => Lvalue::Idx(var, suffix.try_into()?),
            _ => unreachable!(),
        };
    }
    Ok(lvalue)
}

pub(crate) fn parse_expr(pairs: Pairs<Rule>) -> Result<Expr, Error> {
    let mut exprs = LinkedList::new();
    let mut ops: LinkedList<WithPos<Op>> = LinkedList::new();
    for pair in pairs {
        match pair.as_rule() {
            Rule::opexp => exprs.push_back(parse_expr(pair.into_inner())?),
            rule @ (Rule::mul
            | Rule::div
            | Rule::add
            | Rule::sub
            | Rule::gt
            | Rule::ge
            | Rule::lt
            | Rule::le
            | Rule::ne
            | Rule::eq
            | Rule::and
            | Rule::or) => {
                let op = match rule {
                    Rule::add => Op::Add,
                    Rule::sub => Op::Sub,
                    Rule::mul => Op::Mul,
                    Rule::div => Op::Div,
                    Rule::gt => Op::Gt,
                    Rule::ge => Op::Ge,
                    Rule::lt => Op::Lt,
                    Rule::le => Op::Le,
                    Rule::ne => Op::Ne,
                    Rule::eq => Op::Eq,
                    Rule::and => Op::And,
                    Rule::or => Op::Or,
                    _ => unreachable!(),
                };
                loop {
                    match ops.back() {
                        Some(last) if priority(**last) >= priority(op) => {
                            apply(ops.pop_back().unwrap(), &mut exprs)
                        }
                        _ => break,
                    }
                }
                ops.push_back(WithPos {
                    inner: op,
                    pos: pair.line_col().into(),
                });
            }
            Rule::lvalue => exprs.push_back(Expr::Lvalue(pair.try_into()?)),
            Rule::nil => exprs.push_back(Expr::Nil),
            Rule::seq => {
                exprs.push_back(Expr::Seq(
                    pair.into_inner()
                        .map(|pair| parse_expr(pair.into_inner()))
                        .try_collect()?,
                ));
            }
            Rule::int => exprs.push_back(Expr::Integer(pair.as_str().parse::<isize>().map_err(
                |inner| {
                    Error::ParseIntError(WithPos {
                        inner,
                        pos: pair.line_col().into(),
                    })
                },
            )?)),
            Rule::neg => exprs.push_back(Expr::Neg(pair.try_into()?)),
            Rule::string => {
                let s = pair.as_str();
                let mut string = String::new();
                let mut has_escape_char = false;
                for pair in pair.into_inner() {
                    let mut escape = true;
                    match pair.as_rule() {
                        Rule::newline => string.push('\n'),
                        Rule::tab => string.push('\t'),
                        Rule::ctrl => string.push(match pair.as_str().chars().last().unwrap() {
                            ctrl @ 'A'..='Z' => ctrl as u8 - 'A' as u8 + 1,
                            '[' => 27,
                            '\\' => 28,
                            ']' => 29,
                            '^' => 30,
                            '_' => 31,
                            '?' => 127,
                            _ => unreachable!(),
                        } as char),
                        Rule::decimal => {
                            string.push(pair.as_str()[1..].parse::<u8>().unwrap() as char)
                        }
                        Rule::quote => string.push('"'),
                        Rule::escape => string.push('\\'),
                        Rule::ignore => (),
                        Rule::char => {
                            escape = false;
                            string.push_str(pair.as_str())
                        }
                        _ => unreachable!(),
                    }
                    has_escape_char |= escape;
                }
                exprs.push_back(Expr::String(if has_escape_char {
                    Cow::Owned(string)
                } else {
                    Cow::Borrowed(s)
                }))
            }
            Rule::fncall => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::FnCall {
                    name: pairs.next().unwrap().into(),
                    args: pairs.map(|pair| pair.try_into()).try_collect()?,
                });
            }
            Rule::rec => {
                let mut pairs = pair.into_inner();
                let ty = pairs.next().unwrap().into();
                let mut fields = Vec::new();
                while let Some(field) = pairs.next() {
                    fields.push((field.into(), pairs.next().unwrap().try_into()?));
                }
                exprs.push_back(Expr::Rec { ty, fields });
            }
            Rule::array => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::Array {
                    ty: pairs.next().unwrap().into(),
                    n: pairs.next().unwrap().try_into()?,
                    v: pairs.next().unwrap().try_into()?,
                });
            }
            Rule::assign => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::Assign(
                    pairs.next().unwrap().try_into()?,
                    pairs.next().unwrap().try_into()?,
                ));
            }
            Rule::r#if => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::If(
                    pairs.next().unwrap().try_into()?,
                    pairs.next().unwrap().try_into()?,
                    pairs
                        .next()
                        .map(TryInto::try_into)
                        .transpose()?
                        .map(Box::new),
                ));
            }
            Rule::r#while => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::While(
                    pairs.next().unwrap().try_into()?,
                    pairs.next().unwrap().try_into()?,
                ));
            }
            Rule::r#for => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::For(
                    pairs.next().unwrap().as_str().into(),
                    pairs.next().unwrap().try_into()?,
                    pairs.next().unwrap().try_into()?,
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                ));
            }
            Rule::r#break => exprs.push_back(Expr::Break(pair.line_col().into())),
            Rule::r#let => {
                let mut decs = Vec::new();
                let mut pairs = pair.into_inner().peekable();
                while let Some(pair) = pairs.next() {
                    if pairs.peek().is_none() {
                        exprs.push_back(Expr::Let(
                            decs,
                            Expr::Seq(
                                pair.into_inner()
                                    .map(|pair| parse_expr(pair.into_inner()))
                                    .try_collect()?,
                            )
                            .into(),
                        ));
                        break;
                    }
                    match pair.as_rule() {
                        Rule::tydec => {
                            let mut pairs = pair.into_inner();
                            let ident = pairs.next().unwrap().as_str().into();
                            let ty = pairs.next().unwrap();
                            decs.push(Dec::TyDec(
                                ident,
                                WithPos {
                                    pos: ty.line_col().into(),
                                    inner: match ty.as_rule() {
                                        Rule::arraydec => {
                                            Type::Array(ty.into_inner().next().unwrap().into())
                                        }
                                        Rule::recdec => {
                                            Type::Rec(parse_fields(ty.into_inner().next().unwrap()))
                                        }
                                        Rule::ident => Type::Type(ty.into()),
                                        _ => unreachable!(),
                                    },
                                },
                            ));
                        }
                        Rule::vardec => {
                            let mut pairs = pair.into_inner();
                            let name = pairs.next().unwrap();
                            let pair = pairs.next().unwrap();
                            match pair.as_rule() {
                                Rule::ident => decs.push(Dec::VarDec {
                                    name: name.into(),
                                    ty: Some(pair.into()),
                                    val: pairs.next().unwrap().try_into()?,
                                }),
                                Rule::opexp => decs.push(Dec::VarDec {
                                    name: name.into(),
                                    ty: None,
                                    val: pair.try_into()?,
                                }),
                                _ => unreachable!(),
                            }
                        }
                        Rule::fundec => {
                            let mut pairs = pair.into_inner();
                            let name = pairs.next().unwrap().as_str();
                            let fields = parse_fields(pairs.next().unwrap());
                            let pair = pairs.next().unwrap();
                            match pair.as_rule() {
                                Rule::ident => decs.push(Dec::FnDec {
                                    name: name.into(),
                                    retty: Some(pair.into()),
                                    body: pairs.next().unwrap().try_into()?,
                                    fields,
                                }),
                                Rule::opexp => decs.push(Dec::FnDec {
                                    name: name.into(),
                                    retty: None,
                                    body: pair.try_into()?,
                                    fields,
                                }),
                                _ => unreachable!(),
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
            Rule::EOI => (),
            _ => unreachable!(),
        }
    }
    while let Some(op) = ops.pop_back() {
        apply(op, &mut exprs);
    }
    match exprs.pop_back() {
        Some(expr) if exprs.is_empty() => Ok(expr),
        _ => unreachable!(),
    }
}

pub fn parse(src: &str) -> Result<Expr, Error> {
    parse_expr(
        TigerParser::parse(Rule::main, src)
            .map_err(Error::ParseError)?
            .next()
            .unwrap()
            .into_inner(),
    )
}
