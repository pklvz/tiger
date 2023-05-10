use crate::{
    ast::{Dec, Expr, Lvalue, Op, WithPos},
    env::Env,
    error::Error,
};
use anyhow::Result;
use std::{
    collections::HashMap,
    fmt::Debug,
    io::{Read, Write},
    iter::once,
    rc::Rc,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Fn<'a> {
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
        fields: Vec<&'a str>,
        body: Box<WithPos<Expr<'a>>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a> {
    Void,
    Integer(isize),
    String(String),
    Nil,
    Array(Rc<Option<Vec<Value<'a>>>>),
    Rec(Rc<Option<HashMap<&'a str, Value<'a>>>>),
}

impl<'a> Value<'a> {
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

struct Interpreter<'a> {
    venv: Env<'a, Value<'a>>,
    fenv: Env<'a, Fn<'a>>,
}

impl<'a> Interpreter<'a> {
    fn new() -> Self {
        let venv = Env::new();
        let mut fenv = Env::new();
        fenv.insert("print", Fn::Print);
        fenv.insert("flush", Fn::Flush);
        fenv.insert("getchar", Fn::Getchar);
        fenv.insert("ord", Fn::Ord);
        fenv.insert("chr", Fn::Chr);
        fenv.insert("size", Fn::Size);
        fenv.insert("substring", Fn::Substring);
        fenv.insert("concat", Fn::Concat);
        fenv.insert("not", Fn::Not);
        fenv.insert("exit", Fn::Exit);
        Self { venv, fenv }
    }

    fn resolve_lvalue(&mut self, lvalue: &Lvalue<'a>) -> Result<&mut Value<'a>, Error> {
        match lvalue {
            Lvalue::Var(var) => Ok(self.venv.get_mut(var).unwrap()),
            Lvalue::Rec(var, field) => match &mut *self.resolve_lvalue(var)? {
                Value::Rec(ref mut fields) => Ok(unsafe { Rc::get_mut_unchecked(fields) }
                    .as_mut()
                    .ok_or_else(|| Error::DerefNilStruct(field.pos))?
                    .get_mut(**field)
                    .unwrap()),
                _ => unreachable!(),
            },
            Lvalue::Idx(var, idx) => {
                let i = self.eval(idx)?.as_int();
                let i = if i >= 0 {
                    i as usize
                } else {
                    return Err(Error::NegtiveIndex(idx.with_inner(i)));
                };
                match &mut *self.resolve_lvalue(var)? {
                    Value::Array(ref mut a) => Ok(unsafe { Rc::get_mut_unchecked(a) }
                        .as_mut()
                        .ok_or_else(|| Error::DerefNilArray(idx.pos))?
                        .get_mut(i)
                        .ok_or_else(|| Error::IndexOutOfRange(idx.with_inner(i)))?),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn eval_vardec(&mut self, decs: &Vec<Dec<'a>>) -> Result<(Vec<String>, Vec<String>), Error> {
        let mut vnames = Vec::new();
        let mut fnames = Vec::new();
        for dec in decs {
            match dec {
                Dec::VarDec { name, val, .. } => {
                    vnames.push(name.to_string());
                    let val = self.eval(val)?;
                    self.venv.insert(name, val);
                }
                Dec::FnDec {
                    name, fields, body, ..
                } => {
                    fnames.push(name.to_string());
                    self.fenv.insert(
                        name,
                        Fn::Other {
                            fields: fields.into_iter().map(|field| field.name).collect(),
                            body: body.clone(),
                        }
                        .into(),
                    );
                }
                _ => (),
            }
        }
        Ok((vnames, fnames))
    }

    fn eval(&mut self, expr: &Expr<'a>) -> Result<Value<'a>, Error> {
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
            Expr::String(string) => Ok(Value::String(string.to_string())),
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
                        Err(Error::Break) => break,
                        other => other?,
                    };
                }
                Ok(Value::Void)
            }
            Expr::For(name, begin, end, body) => {
                let begin = self.eval(begin)?.as_int();
                let end = self.eval(end)?.as_int();
                for i in begin..=end {
                    self.venv.insert(name, Value::Integer(i));
                    match self.eval(body) {
                        Err(Error::Break) => break,
                        other => other?,
                    };
                    self.venv.remove(name);
                }
                Ok(Value::Void)
            }
            Expr::Break(_) => Err(Error::Break),
            Expr::Let(decs, expr) => {
                let (vnames, fnames) = self.eval_vardec(decs)?;
                let value = self.eval(expr);
                for vname in vnames {
                    self.venv.remove(&vname);
                }
                for fname in fnames {
                    self.fenv.remove(&fname);
                }
                value
            }
            Expr::FnCall { name, args } => {
                let val = self.fenv.get(name).unwrap().clone();
                let mut args: Vec<_> = args.into_iter().map(|arg| self.eval(arg)).try_collect()?;
                match val {
                    Fn::Print => {
                        print!("{}", args.pop().unwrap().as_string());
                        Ok(Value::Void)
                    }
                    Fn::Flush => {
                        std::io::stdout()
                            .flush()
                            .map_err(|error| Error::IOError(name.with_inner(error)))?;
                        Ok(Value::Void)
                    }
                    Fn::Getchar => {
                        let mut buf = [0u8];
                        Ok(Value::String(
                            if std::io::stdin()
                                .read(&mut buf[..])
                                .map_err(|error| Error::IOError(name.with_inner(error)))?
                                == 0
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
                        u8::try_from(args.pop().unwrap().as_int())
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?,
                    )))),
                    Fn::Size => Ok(Value::Integer(
                        args.pop()
                            .unwrap()
                            .as_string()
                            .len()
                            .try_into()
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?,
                    )),
                    Fn::Substring => {
                        let n = usize::try_from(args.pop().unwrap().as_int())
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?;
                        let first = usize::try_from(args.pop().unwrap().as_int())
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?;
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
                        args.pop()
                            .unwrap()
                            .as_int()
                            .try_into()
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?,
                    ),
                    Fn::Other { fields, body } => {
                        for (field, arg) in fields.iter().zip(args) {
                            self.venv.insert(field, arg);
                        }
                        let ret = self.eval(&body)?;
                        for name in fields.iter() {
                            self.venv.remove(name);
                        }
                        Ok(ret)
                    }
                }
            }
            Expr::Rec { fields, .. } => {
                let mut rec = HashMap::new();
                for (field, val) in fields {
                    rec.insert(field.inner, self.eval(val)?);
                }
                Ok(Value::Rec(Rc::new(Some(rec))))
            }
            Expr::Array { n, v, .. } => {
                let len = self.eval(n)?.as_int();
                let len = if len >= 0 {
                    len as usize
                } else {
                    return Err(Error::NegtiveIndex(n.with_inner(len)));
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

pub fn eval<'a>(expr: &'a Expr) -> Result<Value<'a>, Error> {
    Interpreter::new().eval(expr)
}
