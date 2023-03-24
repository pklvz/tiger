use crate::ast::{Dec, Expr, Field, Lvalue, Op, Type, WithPos};
use anyhow::Result;
use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use std::{collections::LinkedList, ops::Deref};

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

fn to_op(rule: Rule) -> Op {
    match rule {
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
    }
}

fn parse_fields(pair: Pair<Rule>) -> Vec<Field> {
    let mut pairs = pair.into_inner();
    let mut fields = Vec::new();
    while let Some(field) = pairs.next() {
        fields.push(Field {
            name: field.as_str().into(),
            ty: pairs.next().unwrap().into(),
        });
    }
    fields
}

pub(crate) fn parse_lvalue(pair: Pair<Rule>) -> Result<Lvalue> {
    let mut pairs = pair.into_inner();
    let mut lvalue = Lvalue::Var(pairs.next().unwrap().into());
    for suffix in pairs {
        match suffix.as_rule() {
            Rule::lvaluefield => {
                lvalue = Lvalue::Rec(lvalue.into(), suffix.into_inner().next().unwrap().into());
            }
            Rule::lvalueidx => {
                lvalue = Lvalue::Idx(lvalue.into(), suffix.try_into()?);
            }
            _ => unreachable!(),
        }
    }
    Ok(lvalue)
}

pub(crate) fn parse_expr(pairs: Pairs<Rule>) -> Result<Expr> {
    let mut exprs = LinkedList::new();
    let mut ops = LinkedList::new();
    for pair in pairs {
        match pair.as_rule() {
            Rule::opexp => exprs.push_back(parse_expr(pair.into_inner())?),
            rule @ (Rule::mul | Rule::div) => {
                while let Some(Op::Mul | Op::Div) = ops.back().map(Deref::deref) {
                    apply(ops.pop_back().unwrap(), &mut exprs);
                }
                ops.push_back(to_op(rule).with_pos(pair));
            }
            rule @ (Rule::add | Rule::sub) => {
                while let Some(Op::Add | Op::Sub | Op::Mul | Op::Div) = ops.back().map(Deref::deref)
                {
                    apply(ops.pop_back().unwrap(), &mut exprs);
                }
                ops.push_back(to_op(rule).with_pos(pair));
            }
            rule @ (Rule::gt | Rule::ge | Rule::lt | Rule::le | Rule::ne | Rule::eq) => {
                loop {
                    match ops.back().map(Deref::deref) {
                        Some(Op::And | Op::Or) | None => break,
                        _ => apply(ops.pop_back().unwrap(), &mut exprs),
                    }
                }
                ops.push_back(to_op(rule).with_pos(pair));
            }
            rule @ Rule::and => {
                loop {
                    match ops.back().map(Deref::deref) {
                        Some(Op::Or) | None => break,
                        _ => apply(ops.pop_back().unwrap(), &mut exprs),
                    }
                }
                ops.push_back(to_op(rule).with_pos(pair));
            }
            rule @ Rule::or => {
                while let Some(op) = ops.pop_back() {
                    apply(op, &mut exprs);
                }
                ops.push_back(to_op(rule).with_pos(pair));
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
            Rule::int => exprs.push_back(Expr::Integer(match pair.as_str().strip_prefix('-') {
                Some(s) => -s.trim().parse()?,
                None => pair.as_str().trim().parse()?,
            })),
            Rule::neg => exprs.push_back(Expr::Neg(pair.try_into()?)),
            Rule::string => exprs.push_back(Expr::String(serde_json::from_str(pair.as_str())?)),
            Rule::fncall => {
                let mut pairs = pair.into_inner();
                let name = pairs.next().unwrap();
                exprs.push_back(Expr::FnCall {
                    name: name.into(),
                    args: pairs.map(|pair| pair.try_into()).try_collect()?,
                });
            }
            Rule::rec => {
                let mut pairs = pair.into_inner();
                let ty = pairs.next().unwrap();
                let mut fields = Vec::new();
                while let Some(field) = pairs.next() {
                    fields.push((field.into(), pairs.next().unwrap().try_into()?));
                }
                exprs.push_back(Expr::Rec {
                    ty: ty.into(),
                    fields,
                });
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
            Rule::r#break => exprs.push_back(Expr::Break(WithPos {
                pos: pair.line_col().into(),
                inner: (),
            })),
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

pub fn parse(src: &str) -> Result<Expr> {
    parse_expr(
        TigerParser::parse(Rule::main, src)?
            .next()
            .unwrap()
            .into_inner(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::anyhow;
    use std::fs;
    use test::Bencher;

    #[test]
    fn test_samples() -> Result<()> {
        for sample in fs::read_dir("samples")? {
            let sample = sample?;
            let result = parse(&fs::read_to_string(sample.path())?);
            if sample.file_name() == "test49.tig" {
                assert!(result.is_err());
            } else if let Err(error) = result {
                return Err(anyhow!("Parse {:?}: {}", sample.file_name(), error));
            }
        }
        Ok(())
    }

    #[bench]
    fn bench_samples(b: &mut Bencher) -> Result<()> {
        let samples: Vec<_> = fs::read_dir("samples")?
            .into_iter()
            .map(|sample| fs::read_to_string(sample?.path()))
            .try_collect()?;
        b.iter(|| {
            for sample in &samples {
                _ = parse(sample);
            }
        });
        Ok(())
    }
}
