use crate::{
    ast::{Dec, Expr, Field, Lvalue, Op, Type, WithPos},
    error::Error,
};
use pest::{iterators::Pair, pratt_parser::PrattParser, Parser};
use std::borrow::Cow;

#[derive(Parser)]
#[grammar = "tiger.pest"]
struct TigerParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        PrattParser::new()
            .op(Op::prefix(minus))
            .op(Op::infix(or, Left))
            .op(Op::infix(and, Left))
            .op(Op::infix(gt, Left)
                | Op::infix(ge, Left)
                | Op::infix(lt, Left)
                | Op::infix(le, Left)
                | Op::infix(ne, Left)
                | Op::infix(eq, Left))
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left))
    };
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
            Rule::lvalueidx => Lvalue::Idx(var, suffix.into_inner().next().unwrap().try_into()?),
            _ => unreachable!(),
        };
    }
    Ok(lvalue)
}

pub(crate) fn parse_expr(pair: Pair<Rule>) -> Result<Expr, Error> {
    match pair.as_rule() {
        Rule::exp => PRATT_PARSER
            .map_primary(parse_expr)
            .map_infix(|lhs, op, rhs| {
                Ok(Expr::BinOp {
                    lhs: lhs?.into(),
                    rhs: rhs?.into(),
                    op: WithPos {
                        pos: op.line_col().into(),
                        inner: match op.as_rule() {
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
                        },
                    },
                })
            })
            .map_prefix(|op, expr| match op.as_rule() {
                Rule::minus => Ok(Expr::Neg(
                    WithPos {
                        inner: expr?,
                        pos: op.line_col().into(),
                    }
                    .into(),
                )),
                _ => unreachable!(),
            })
            .parse(pair.into_inner()),
        Rule::lvalue => Ok(Expr::Lvalue(pair.try_into()?)),
        Rule::nil => Ok(Expr::Nil),
        Rule::seq => Ok(Expr::Seq(pair.into_inner().map(parse_expr).try_collect()?)),
        Rule::int => Ok(Expr::Integer(pair.as_str().parse::<isize>().map_err(
            |inner| {
                Error::ParseIntError(WithPos {
                    inner,
                    pos: pair.line_col().into(),
                })
            },
        )?)),
        Rule::string => {
            let s = pair.as_str();
            let s = &s[1..s.len() - 1];
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
                    Rule::decimal => string.push(pair.as_str()[1..].parse::<u8>().unwrap() as char),
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
            Ok(Expr::String(if has_escape_char {
                Cow::Owned(string)
            } else {
                Cow::Borrowed(s)
            }))
        }
        Rule::fncall => {
            let mut pairs = pair.into_inner();
            Ok(Expr::FnCall {
                name: pairs.next().unwrap().into(),
                args: pairs.map(|pair| pair.try_into()).try_collect()?,
            })
        }
        Rule::rec => {
            let mut pairs = pair.into_inner();
            let ty = pairs.next().unwrap().into();
            let mut fields = Vec::new();
            while let Some(field) = pairs.next() {
                fields.push((field.into(), pairs.next().unwrap().try_into()?));
            }
            Ok(Expr::Rec { ty, fields })
        }
        Rule::array => {
            let mut pairs = pair.into_inner();
            Ok(Expr::Array {
                ty: pairs.next().unwrap().into(),
                n: pairs.next().unwrap().try_into()?,
                v: pairs.next().unwrap().try_into()?,
            })
        }
        Rule::assign => {
            let mut pairs = pair.into_inner();
            Ok(Expr::Assign(
                pairs.next().unwrap().try_into()?,
                pairs.next().unwrap().try_into()?,
            ))
        }
        Rule::r#if => {
            let mut pairs = pair.into_inner();
            Ok(Expr::If(
                pairs.next().unwrap().try_into()?,
                pairs.next().unwrap().try_into()?,
                pairs
                    .next()
                    .map(TryInto::try_into)
                    .transpose()?
                    .map(Box::new),
            ))
        }
        Rule::r#while => {
            let mut pairs = pair.into_inner();
            Ok(Expr::While(
                pairs.next().unwrap().try_into()?,
                pairs.next().unwrap().try_into()?,
            ))
        }
        Rule::r#for => {
            let mut pairs = pair.into_inner();
            Ok(Expr::For(
                pairs.next().unwrap().as_str().into(),
                pairs.next().unwrap().try_into()?,
                pairs.next().unwrap().try_into()?,
                parse_expr(pairs.next().unwrap())?.into(),
            ))
        }
        Rule::r#break => Ok(Expr::Break(pair.line_col().into())),
        Rule::r#let => {
            let mut decs = Vec::new();
            let mut pairs = pair.into_inner().peekable();
            while let Some(pair) = pairs.next() {
                if pairs.peek().is_none() {
                    return Ok(Expr::Let(
                        decs,
                        Expr::Seq(pair.into_inner().map(parse_expr).try_collect()?).into(),
                    ));
                }
                decs.push(match pair.as_rule() {
                    Rule::tydec => {
                        let mut pairs = pair.into_inner();
                        let name = pairs.next().unwrap().as_str().into();
                        let ty = pairs.next().unwrap();
                        Dec::TyDec {
                            name,
                            ty: WithPos {
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
                        }
                    }
                    Rule::vardec => {
                        let mut pairs = pair.into_inner();
                        let name = pairs.next().unwrap().into();
                        let pair = pairs.next().unwrap();
                        match pair.as_rule() {
                            Rule::ident => Dec::VarDec {
                                name,
                                ty: Some(pair.into()),
                                val: pairs.next().unwrap().try_into()?,
                            },
                            Rule::exp => Dec::VarDec {
                                name,
                                ty: None,
                                val: pair.try_into()?,
                            },
                            _ => unreachable!(),
                        }
                    }
                    Rule::fundec => {
                        let mut pairs = pair.into_inner();
                        let name = pairs.next().unwrap().as_str().into();
                        let fields = parse_fields(pairs.next().unwrap());
                        let pair = pairs.next().unwrap();
                        match pair.as_rule() {
                            Rule::ident => Dec::FnDec {
                                name,
                                fields,
                                retty: Some(pair.into()),
                                body: pairs.next().unwrap().try_into()?,
                            },
                            Rule::exp => Dec::FnDec {
                                name,
                                fields,
                                retty: None,
                                body: pair.try_into()?,
                            },
                            _ => unreachable!(),
                        }
                    }
                    _ => unreachable!(),
                });
            }
            Ok(Expr::Let(decs, Expr::Seq(Vec::new()).into()))
        }
        _ => unreachable!(),
    }
}

pub fn parse(src: &str) -> Result<Expr, Error> {
    parse_expr(
        TigerParser::parse(Rule::main, src)
            .map_err(Error::ParseError)?
            .next()
            .unwrap()
            .into_inner()
            .next()
            .unwrap(),
    )
}
