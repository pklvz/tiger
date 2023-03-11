use crate::ast::{Dec, Expr, Field, Lvalue, Op, Type};
use anyhow::Result;
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use std::collections::LinkedList;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "tiger.pest"]
struct TigerParser;

#[derive(Error, Debug)]
enum SyntaxError {
    #[error("incomplete expression")]
    IncompleteExpression,
    #[error("multiple expressions without delimiter")]
    MultipleExpressions,
}

fn apply(op: Op, exprs: &mut LinkedList<Expr>) -> Result<()> {
    let rhs = exprs.pop_back().ok_or(SyntaxError::IncompleteExpression)?;
    let lhs = exprs.pop_back().ok_or(SyntaxError::IncompleteExpression)?;
    exprs.push_back(Expr::BinOp {
        lhs: lhs.into(),
        rhs: rhs.into(),
        op,
    });
    Ok(())
}

fn rule_to_op(rule: Rule) -> Op {
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
            ty: pairs.next().unwrap().as_str().into(),
        });
    }
    fields
}

fn parse_lvalue(pair: Pair<Rule>) -> Result<Lvalue> {
    let mut pairs = pair.into_inner();
    let mut lvalue = Lvalue::Var(pairs.next().unwrap().as_str().into());
    for suffix in pairs {
        match suffix.as_rule() {
            Rule::lvaluefield => {
                lvalue = Lvalue::Rec(
                    lvalue.into(),
                    suffix.into_inner().next().unwrap().as_str().into(),
                );
            }
            Rule::lvalueidx => {
                lvalue = Lvalue::Idx(lvalue.into(), parse_expr(suffix.into_inner())?.into());
            }
            _ => unreachable!(),
        }
    }
    Ok(lvalue)
}

fn parse_expr(pairs: Pairs<Rule>) -> Result<Expr> {
    let mut exprs = LinkedList::new();
    let mut ops = LinkedList::new();
    for pair in pairs {
        match pair.as_rule() {
            Rule::opexp => exprs.push_back(parse_expr(pair.into_inner())?),
            rule @ (Rule::mul | Rule::div) => {
                while let Some(Op::Mul | Op::Div) = ops.back() {
                    apply(ops.pop_back().unwrap(), &mut exprs)?;
                }
                ops.push_back(rule_to_op(rule));
            }
            rule @ (Rule::add | Rule::sub) => {
                while let Some(Op::Add | Op::Sub | Op::Mul | Op::Div) = ops.back() {
                    apply(ops.pop_back().unwrap(), &mut exprs)?;
                }
                ops.push_back(rule_to_op(rule));
            }
            rule @ (Rule::gt | Rule::ge | Rule::lt | Rule::le | Rule::ne | Rule::eq) => {
                loop {
                    match ops.back() {
                        Some(Op::And | Op::Or) | None => break,
                        _ => apply(ops.pop_back().unwrap(), &mut exprs)?,
                    }
                }
                ops.push_back(rule_to_op(rule));
            }
            rule @ Rule::and => {
                loop {
                    match ops.back() {
                        Some(Op::Or) | None => break,
                        _ => apply(ops.pop_back().unwrap(), &mut exprs)?,
                    }
                }
                ops.push_back(rule_to_op(rule));
            }
            rule @ Rule::or => {
                while let Some(op) = ops.pop_back() {
                    apply(op, &mut exprs)?;
                }
                ops.push_back(rule_to_op(rule));
            }
            Rule::lvalue => exprs.push_back(Expr::Lvalue(parse_lvalue(pair)?)),
            Rule::nil => exprs.push_back(Expr::Nil),
            Rule::seq => {
                exprs.push_back(Expr::Seq(
                    pair.into_inner()
                        .map(|pairs| parse_expr(pairs.into_inner()))
                        .try_collect()?,
                ));
            }
            Rule::int => exprs.push_back(Expr::Integer(match pair.as_str().strip_prefix('-') {
                Some(s) => -s.trim().parse()?,
                None => pair.as_str().trim().parse()?,
            })),
            Rule::neg => exprs.push_back(Expr::Neg(parse_expr(pair.into_inner())?.into())),
            Rule::string => exprs.push_back(Expr::String(serde_json::from_str(pair.as_str())?)),
            Rule::fncall => {
                let mut pairs = pair.into_inner();
                let name = pairs.next().unwrap().as_str();
                exprs.push_back(Expr::FnCall {
                    name: name.into(),
                    args: pairs
                        .map(|pairs| parse_expr(pairs.into_inner()))
                        .try_collect()?,
                });
            }
            Rule::rec => {
                let mut pairs = pair.into_inner();
                let ty = pairs.next().unwrap().as_str();
                let mut fields = Vec::new();
                while let Some(field) = pairs.next() {
                    fields.push((
                        field.as_str().into(),
                        parse_expr(pairs.next().unwrap().into_inner())?,
                    ));
                }
                exprs.push_back(Expr::Rec {
                    ty: ty.into(),
                    fields,
                });
            }
            Rule::array => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::Array {
                    ty: pairs.next().unwrap().as_str().into(),
                    n: parse_expr(pairs.next().unwrap().into_inner())?.into(),
                    v: parse_expr(pairs.next().unwrap().into_inner())?.into(),
                });
            }
            Rule::assign => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::Assign(
                    parse_lvalue(pairs.next().unwrap())?,
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                ));
            }
            Rule::r#if => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::If(
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                    pairs
                        .next()
                        .map(|pair| parse_expr(pair.into_inner()))
                        .transpose()?
                        .map(Box::new),
                ));
            }
            Rule::r#while => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::While(
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                ));
            }
            Rule::r#for => {
                let mut pairs = pair.into_inner();
                exprs.push_back(Expr::For(
                    pairs.next().unwrap().as_str().into(),
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                    parse_expr(pairs.next().unwrap().into_inner())?.into(),
                ));
            }
            Rule::r#break => exprs.push_back(Expr::Break),
            Rule::r#let => {
                let mut decs = Vec::new();
                let mut pairs = pair.into_inner().peekable();
                while let Some(pair) = pairs.next() {
                    if pairs.peek().is_none() {
                        exprs.push_back(Expr::Let(
                            decs,
                            Expr::Seq(
                                pair.into_inner()
                                    .map(|pairs| parse_expr(pairs.into_inner()))
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
                            let ty = match ty.as_rule() {
                                Rule::arraydec => {
                                    Type::Array(ty.into_inner().next().unwrap().as_str().into())
                                }
                                Rule::recdec => {
                                    Type::Rec(parse_fields(ty.into_inner().next().unwrap()))
                                }
                                Rule::ident => Type::Type(ty.as_str().into()),
                                _ => unreachable!(),
                            };
                            decs.push(Dec::TyDec(ident, ty));
                        }
                        Rule::vardec => {
                            let mut pairs = pair.into_inner();
                            let name = pairs.next().unwrap().as_str();
                            let pair = pairs.next().unwrap();
                            match pair.as_rule() {
                                Rule::ident => decs.push(Dec::VarDec {
                                    name: name.into(),
                                    ty: Some(pair.as_str().into()),
                                    val: parse_expr(pairs.next().unwrap().into_inner())?.into(),
                                }),
                                Rule::opexp => decs.push(Dec::VarDec {
                                    name: name.into(),
                                    ty: None,
                                    val: parse_expr(pair.into_inner())?.into(),
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
                                    retty: Some(pair.as_str().into()),
                                    body: parse_expr(pairs.next().unwrap().into_inner())?.into(),
                                    fields,
                                }),
                                Rule::opexp => decs.push(Dec::FnDec {
                                    name: name.into(),
                                    retty: None,
                                    body: parse_expr(pair.into_inner())?.into(),
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
        apply(op, &mut exprs)?;
    }
    if exprs.len() != 1 {
        return Err(SyntaxError::MultipleExpressions.into());
    }
    Ok(exprs.into_iter().next().unwrap())
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
