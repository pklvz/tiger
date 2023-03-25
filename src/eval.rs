use crate::{
    ast::{Dec, Expr, Lvalue, Op, Pos, WithPos},
    env::Env,
};
use anyhow::Result;
use std::{
    collections::HashMap,
    fmt::Debug,
    io::{self, Read, Write},
    iter::once,
    num,
    rc::Rc,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum RuntimeError {
    #[error("{}, nil struct dereference", .0)]
    DerefNilStruct(Pos),
    #[error("{}, nil array dereference", .0)]
    DerefNilArray(Pos),
    #[error("{}, negative index: {}", .0.pos, .0.inner)]
    NegtiveIndex(WithPos<isize>),
    #[error("{}, index out of range: {}", .0.pos, .0.inner)]
    IndexOutOfRange(WithPos<usize>),
    #[error("{}, {}", .0.pos, .0.inner)]
    IOError(WithPos<io::Error>),
    #[error("{}, {}", .0.pos, .0.inner)]
    TryFromIntError(WithPos<num::TryFromIntError>),
    #[error("")]
    Break,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Fn {
    Print,
    Flush,
    Getchar,
    Ord,
    Chr,
    Size,
    Substring,
    Concat,
    Not,
    Exit,
    Other {
        fields: Vec<String>,
        body: Box<WithPos<Expr>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Void,
    Integer(isize),
    String(String),
    Nil,
    Array(Rc<Option<Vec<Value>>>),
    Rec(Rc<Option<HashMap<String, Value>>>),
    Fn(Fn),
}

impl Value {
    fn as_int(self) -> isize {
        match self {
            Value::Integer(int) => int,
            _ => unreachable!(),
        }
    }

    fn as_string(self) -> String {
        match self {
            Value::String(string) => string,
            _ => unreachable!(),
        }
    }
}

struct Interpreter {
    venv: Env<Value>,
}

impl Interpreter {
    fn new() -> Self {
        let mut venv = Env::new();
        venv.insert("print".into(), Value::Fn(Fn::Print));
        venv.insert("flush".into(), Value::Fn(Fn::Flush));
        venv.insert("getchar".into(), Value::Fn(Fn::Getchar));
        venv.insert("ord".into(), Value::Fn(Fn::Ord));
        venv.insert("chr".into(), Value::Fn(Fn::Chr));
        venv.insert("size".into(), Value::Fn(Fn::Size));
        venv.insert("substring".into(), Value::Fn(Fn::Substring));
        venv.insert("concat".into(), Value::Fn(Fn::Concat));
        venv.insert("not".into(), Value::Fn(Fn::Not));
        venv.insert("exit".into(), Value::Fn(Fn::Exit));
        Self { venv }
    }

    fn resolve_lvalue(&mut self, lvalue: &Lvalue) -> Result<&mut Value, RuntimeError> {
        match lvalue {
            Lvalue::Var(var) => Ok(self.venv.get_mut(var).unwrap()),
            Lvalue::Rec(var, field) => match &mut *self.resolve_lvalue(var)? {
                Value::Rec(ref mut fields) => Ok(unsafe { Rc::get_mut_unchecked(fields) }
                    .as_mut()
                    .ok_or_else(|| RuntimeError::DerefNilStruct(field.pos))?
                    .get_mut(&**field)
                    .unwrap()),
                _ => unreachable!(),
            },
            Lvalue::Idx(var, idx) => {
                let i = self.eval(idx)?.as_int();
                let i = if i >= 0 {
                    i as usize
                } else {
                    return Err(RuntimeError::NegtiveIndex(idx.with_inner(i)));
                };
                match &mut *self.resolve_lvalue(var)? {
                    Value::Array(ref mut a) => Ok(unsafe { Rc::get_mut_unchecked(a) }
                        .as_mut()
                        .ok_or_else(|| RuntimeError::DerefNilArray(idx.pos))?
                        .get_mut(i)
                        .ok_or_else(|| RuntimeError::IndexOutOfRange(idx.with_inner(i)))?),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn eval_vardec(&mut self, decs: &Vec<Dec>) -> Result<(), RuntimeError> {
        for dec in decs {
            match dec {
                Dec::VarDec { name, val, .. } => {
                    let val = self.eval(val)?;
                    self.venv.insert((**name).clone(), val);
                }
                Dec::FnDec {
                    name, fields, body, ..
                } => {
                    self.venv.insert(
                        name.clone(),
                        Value::Fn(Fn::Other {
                            fields: fields.into_iter().map(|field| field.name.clone()).collect(),
                            body: body.clone(),
                        })
                        .into(),
                    );
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn eval(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        match expr {
            Expr::BinOp { lhs, rhs, op } => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;
                Ok(Value::Integer(match (lhs, rhs, &**op) {
                    (Value::String(lhs), Value::String(rhs), Op::Gt) => (lhs > rhs) as isize,
                    (Value::String(lhs), Value::String(rhs), Op::Ge) => (lhs >= rhs) as isize,
                    (Value::String(lhs), Value::String(rhs), Op::Lt) => (lhs < rhs) as isize,
                    (Value::String(lhs), Value::String(rhs), Op::Le) => (lhs <= rhs) as isize,
                    (Value::String(lhs), Value::String(rhs), Op::Ne) => (lhs != rhs) as isize,
                    (Value::String(lhs), Value::String(rhs), Op::Eq) => (lhs == rhs) as isize,

                    (Value::Integer(lhs), Value::Integer(rhs), Op::Gt) => (lhs > rhs) as isize,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Ge) => (lhs >= rhs) as isize,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Lt) => (lhs < rhs) as isize,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Le) => (lhs <= rhs) as isize,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Ne) => (lhs != rhs) as isize,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Eq) => (lhs == rhs) as isize,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Add) => lhs + rhs,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Sub) => lhs - rhs,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Mul) => lhs * rhs,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Div) => lhs / rhs,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::And) => lhs & rhs,
                    (Value::Integer(lhs), Value::Integer(rhs), Op::Or) => lhs | rhs,

                    (Value::Array(lhs), Value::Array(rhs), Op::Ne) => (lhs != rhs) as isize,
                    (Value::Array(lhs), Value::Array(rhs), Op::Eq) => (lhs == rhs) as isize,
                    (Value::Array(lhs), Value::Nil, Op::Ne) => lhs.is_some() as isize,
                    (Value::Array(lhs), Value::Nil, Op::Eq) => lhs.is_none() as isize,
                    (Value::Nil, Value::Array(rhs), Op::Ne) => rhs.is_some() as isize,
                    (Value::Nil, Value::Array(rhs), Op::Eq) => rhs.is_none() as isize,

                    (Value::Rec(lhs), Value::Rec(rhs), Op::Ne) => (lhs != rhs) as isize,
                    (Value::Rec(lhs), Value::Rec(rhs), Op::Eq) => (lhs == rhs) as isize,
                    (Value::Rec(lhs), Value::Nil, Op::Ne) => lhs.is_some() as isize,
                    (Value::Rec(lhs), Value::Nil, Op::Eq) => lhs.is_none() as isize,
                    (Value::Nil, Value::Rec(rhs), Op::Ne) => rhs.is_some() as isize,
                    (Value::Nil, Value::Rec(rhs), Op::Eq) => rhs.is_none() as isize,

                    (Value::Nil, Value::Nil, Op::Ne) => 0,
                    (Value::Nil, Value::Nil, Op::Eq) => 1,

                    _ => unreachable!(),
                }))
            }
            Expr::Nil => Ok(Value::Nil),
            Expr::Neg(expr) => Ok(Value::Integer(-self.eval(expr)?.as_int())),
            Expr::Seq(exprs) => match &exprs[..] {
                [] => Ok(Value::Nil),
                [exprs @ .., expr] => {
                    for expr in exprs {
                        self.eval(expr)?;
                    }
                    self.eval(expr)
                }
            },
            Expr::Integer(int) => Ok(Value::Integer(*int)),
            Expr::String(string) => Ok(Value::String(string.clone())),
            Expr::If(cond, t, f) => {
                let cond = self.eval(cond)?.as_int();
                match f {
                    Some(f) => self.eval(if cond == 0 { f } else { t }),
                    None => {
                        if cond != 0 {
                            self.eval(t)?;
                        }
                        Ok(Value::Void)
                    }
                }
            }
            Expr::While(cond, body) => {
                while self.eval(cond)?.as_int() != 0 {
                    match self.eval(body) {
                        Err(RuntimeError::Break) => break,
                        other => other?,
                    };
                }
                Ok(Value::Void)
            }
            Expr::For(name, begin, end, body) => {
                let begin = self.eval(begin)?.as_int();
                let end = self.eval(end)?.as_int();
                for i in begin..=end {
                    self.venv.insert(name.clone(), Value::Integer(i));
                    match self.eval(body) {
                        Err(RuntimeError::Break) => break,
                        other => other?,
                    };
                    self.venv.remove(name);
                }
                Ok(Value::Void)
            }
            Expr::Break(_) => Err(RuntimeError::Break),
            Expr::Let(decs, expr) => {
                self.eval_vardec(decs)?;
                self.eval(expr)
            }
            Expr::FnCall { name, args } => {
                let val = self.venv.get(name).unwrap().clone();
                let mut args: Vec<_> = args.into_iter().map(|arg| self.eval(arg)).try_collect()?;
                match val {
                    Value::Fn(r#fn) => {
                        match r#fn {
                            Fn::Print => {
                                print!("{}", args.pop().unwrap().as_string());
                                Ok(Value::Void)
                            }
                            Fn::Flush => {
                                std::io::stdout()
                                    .flush()
                                    .map_err(|err| RuntimeError::IOError(name.with_inner(err)))?;
                                Ok(Value::Void)
                            }
                            Fn::Getchar => {
                                let mut buf = [0u8];
                                Ok(Value::String(
                                    if std::io::stdin().read(&mut buf[..]).map_err(|err| {
                                        RuntimeError::IOError(name.with_inner(err))
                                    })? == 0
                                    {
                                        "".into()
                                    } else {
                                        String::from(char::from(buf[0]))
                                    },
                                ))
                            }
                            Fn::Ord => Ok(Value::Integer(
                                args.pop()
                                    .unwrap()
                                    .as_string()
                                    .bytes()
                                    .next()
                                    .map(isize::from)
                                    .unwrap_or(-1),
                            )),
                            Fn::Chr => Ok(Value::String(String::from(char::from(
                                u8::try_from(args.pop().unwrap().as_int()).map_err(|err| {
                                    RuntimeError::TryFromIntError(name.with_inner(err))
                                })?,
                            )))),
                            Fn::Size => Ok(Value::Integer(
                                args.pop().unwrap().as_string().len().try_into().map_err(
                                    |err| RuntimeError::TryFromIntError(name.with_inner(err)),
                                )?,
                            )),
                            Fn::Substring => {
                                let n = usize::try_from(args.pop().unwrap().as_int()).map_err(
                                    |err| RuntimeError::TryFromIntError(name.with_inner(err)),
                                )?;
                                let first = usize::try_from(args.pop().unwrap().as_int()).map_err(
                                    |err| RuntimeError::TryFromIntError(name.with_inner(err)),
                                )?;
                                Ok(Value::String(String::from(
                                    &args.pop().unwrap().as_string()[first..first + n],
                                )))
                            }
                            Fn::Concat => {
                                let s2 = args.pop().unwrap().as_string();
                                let mut s1 = args.pop().unwrap().as_string();
                                s1.push_str(&s2);
                                Ok(Value::String(s1))
                            }
                            Fn::Not => Ok(Value::Integer(if args.pop().unwrap().as_int() == 0 {
                                1
                            } else {
                                0
                            })),
                            Fn::Exit => std::process::exit(
                                args.pop().unwrap().as_int().try_into().map_err(|err| {
                                    RuntimeError::TryFromIntError(name.with_inner(err))
                                })?,
                            ),
                            Fn::Other { fields, body } => {
                                for (field, arg) in fields.iter().zip(args) {
                                    self.venv.insert(field.clone(), arg);
                                }
                                let ret = self.eval(&body)?;
                                for name in fields {
                                    self.venv.remove(&name);
                                }
                                Ok(ret)
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Expr::Rec { fields, .. } => {
                let mut rec = HashMap::new();
                for (field, val) in fields {
                    rec.insert((**field).clone(), self.eval(val)?);
                }
                Ok(Value::Rec(Rc::new(Some(rec))))
            }
            Expr::Array { n, v, .. } => {
                let len = self.eval(n)?.as_int();
                let len = if len >= 0 {
                    len as usize
                } else {
                    return Err(RuntimeError::NegtiveIndex(n.with_inner(len)));
                };
                let v = self.eval(v)?;
                let a = once(v).cycle().take(len).collect();
                Ok(Value::Array(Rc::new(Some(a))))
            }
            Expr::Assign(lvalue, expr) => {
                *self.resolve_lvalue(lvalue)? = self.eval(expr)?;
                Ok(Value::Void)
            }
            Expr::Lvalue(lvalue) => self.resolve_lvalue(lvalue).cloned(),
        }
    }
}

pub fn eval(expr: &Expr) -> Result<Value, RuntimeError> {
    Interpreter::new().eval(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parser::parse, types::check};
    use anyhow::anyhow;
    use std::{collections::HashSet, fs};
    use test::Bencher;

    #[test]
    fn test_samples() -> Result<()> {
        let ignored = HashSet::from([
            "merge.tig",
            "queens.tig",
            "test6.tig",
            "test7.tig",
            "test9.tig",
            "test10.tig",
            "test11.tig",
            "test13.tig",
            "test14.tig",
            "test15.tig",
            "test16.tig",
            "test18.tig",
            "test19.tig",
            "test20.tig",
            "test21.tig",
            "test22.tig",
            "test23.tig",
            "test24.tig",
            "test25.tig",
            "test26.tig",
            "test28.tig",
            "test29.tig",
            "test31.tig",
            "test32.tig",
            "test33.tig",
            "test34.tig",
            "test35.tig",
            "test36.tig",
            "test40.tig",
            "test43.tig",
            "test45.tig",
            "test49.tig",
        ]);
        for sample in fs::read_dir("samples")? {
            let sample = sample?;
            if !ignored.contains(sample.file_name().to_str().unwrap()) {
                if let Err(error) = eval(&parse(&fs::read_to_string(sample.path())?)?) {
                    return Err(anyhow!("Eval {:?}: {}", sample.file_name(), error));
                }
            }
        }
        Ok(())
    }

    #[bench]
    fn bench_samples(b: &mut Bencher) -> Result<()> {
        let ignored = HashSet::from([
            "merge.tig",
            "queens.tig",
            "test6.tig",
            "test7.tig",
            "test18.tig",
        ]);
        let samples: Vec<_> = fs::read_dir("samples")?
            .into_iter()
            .try_collect::<Vec<_>>()?
            .into_iter()
            .filter(|sample| !ignored.contains(sample.file_name().to_str().unwrap()))
            .map(|sample| fs::read_to_string(sample.path()))
            .try_collect::<Vec<_>>()?
            .into_iter()
            .filter_map(|sample| parse(&sample).ok())
            .filter(|expr| check(&expr).is_ok())
            .collect();
        b.iter(|| {
            for sample in &samples {
                _ = eval(sample);
            }
        });
        Ok(())
    }
}
