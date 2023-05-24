use crate::{
    ast::{Dec, Expr, Lvalue, Op, WithPos},
    env::Env,
    error::Error,
};
use std::{
    borrow::Cow,
    collections::HashMap,
    fmt::Debug,
    io::{Read, Write},
    iter::once,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub enum Fun<'a> {
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
    String(Cow<'a, str>),
    Nil,
    Array(Rc<Vec<Value<'a>>>),
    Rec(Rc<HashMap<&'a str, Value<'a>>>),
}

impl<'a> Value<'a> {
    fn as_int(self) -> isize {
        match self {
            Value::Integer(int) => int,
            _ => unreachable!(),
        }
    }

    fn as_string(self) -> Cow<'a, str> {
        match self {
            Value::String(string) => string,
            _ => unreachable!(),
        }
    }
}

impl<'a> WithPos<Value<'a>> {
    fn as_index(self) -> Result<usize, Error> {
        match *self {
            Value::Integer(int) if int >= 0 => Ok(int as usize),
            Value::Integer(int) => Err(Error::NegtiveIndex(self.with_inner(int))),
            _ => unreachable!(),
        }
    }
}

struct Interpreter<'a> {
    venv: Env<'a, Value<'a>>,
    fenv: Env<'a, Fun<'a>>,
}

impl<'a> Interpreter<'a> {
    fn new() -> Self {
        let venv = Env::new();
        let mut fenv = Env::new();
        fenv.insert("print", Fun::Print);
        fenv.insert("flush", Fun::Flush);
        fenv.insert("getchar", Fun::Getchar);
        fenv.insert("ord", Fun::Ord);
        fenv.insert("chr", Fun::Chr);
        fenv.insert("size", Fun::Size);
        fenv.insert("substring", Fun::Substring);
        fenv.insert("concat", Fun::Concat);
        fenv.insert("not", Fun::Not);
        fenv.insert("exit", Fun::Exit);
        Self { venv, fenv }
    }

    fn eval_lvalue(&mut self, lvalue: &Lvalue<'a>) -> Result<&mut Value<'a>, Error> {
        match lvalue {
            Lvalue::Var(var) => Ok(self.venv.get_mut(var).unwrap()),
            Lvalue::Rec(lvalue, field) => match &mut *self.eval_lvalue(lvalue)? {
                Value::Rec(fields) => Ok(unsafe { Rc::get_mut_unchecked(fields) }
                    .get_mut(**field)
                    .unwrap()),
                Value::Nil => Err(Error::DerefNilStruct(field.pos)),
                _ => unreachable!(),
            },
            Lvalue::Idx(lvalue, index) => {
                let i = self.eval_with_pos(index)?.as_index()?;
                match &mut *self.eval_lvalue(lvalue)? {
                    Value::Array(array) => {
                        Ok(unsafe { Rc::get_mut_unchecked(array) }
                            .get_mut(i)
                            .ok_or_else(|| Error::IndexOutOfRange(index.with_inner(i)))?)
                    }
                    Value::Nil => Err(Error::DerefNilArray(index.pos)),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn eval_vardec(&mut self, decs: &Vec<Dec<'a>>) -> Result<(), Error> {
        for dec in decs {
            match dec {
                Dec::VarDec { name, expr, .. } => {
                    let value = self.eval(expr)?;
                    self.venv.insert(name, value);
                }
                Dec::FunDec {
                    name, fields, body, ..
                } => {
                    self.fenv.insert(
                        name,
                        Fun::Other {
                            fields: fields.into_iter().map(|field| field.name).collect(),
                            body: body.clone(),
                        },
                    );
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn eval(&mut self, expr: &Expr<'a>) -> Result<Value<'a>, Error> {
        match expr {
            Expr::BinOp { lhs, rhs, op } => Ok(Value::Integer(match &**op {
                Op::And => match self.eval(lhs)?.as_int() {
                    0 => 0,
                    _ => (self.eval(rhs)?.as_int() != 0) as isize,
                },
                Op::Or => match self.eval(lhs)?.as_int() {
                    0 => (self.eval(rhs)?.as_int() != 0) as isize,
                    _ => 1,
                },
                op => {
                    let lhs = self.eval(lhs)?;
                    let rhs = self.eval(rhs)?;
                    match (lhs, rhs, op) {
                        (Value::String(lhs), Value::String(rhs), Op::Gt) => (lhs > rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Ge) => (lhs >= rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Lt) => (lhs < rhs) as isize,
                        (Value::String(lhs), Value::String(rhs), Op::Le) => (lhs <= rhs) as isize,

                        (Value::Integer(lhs), Value::Integer(rhs), Op::Gt) => (lhs > rhs) as isize,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Ge) => (lhs >= rhs) as isize,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Lt) => (lhs < rhs) as isize,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Le) => (lhs <= rhs) as isize,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Add) => lhs + rhs,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Sub) => lhs - rhs,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Mul) => lhs * rhs,
                        (Value::Integer(lhs), Value::Integer(rhs), Op::Div) => lhs / rhs,

                        (lhs, rhs, Op::Eq) => (lhs == rhs) as isize,
                        (lhs, rhs, Op::Ne) => (lhs != rhs) as isize,
                        _ => unreachable!(),
                    }
                }
            })),
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
                self.eval_vardec(decs)?;
                let value = self.eval(expr);
                for dec in decs {
                    match dec {
                        Dec::VarDec { name, .. } => self.venv.remove(name),
                        Dec::FunDec { name, .. } => self.fenv.remove(name),
                        Dec::TyDec { .. } => (),
                    };
                }
                value
            }
            Expr::FunCall { name, args } => {
                let value = self.fenv.get(name).unwrap().clone();
                let mut args = args.iter();
                match value {
                    Fun::Print => {
                        print!("{}", self.eval(args.next().unwrap())?.as_string());
                        Ok(Value::Void)
                    }
                    Fun::Flush => {
                        std::io::stdout()
                            .flush()
                            .map_err(|error| Error::IOError(name.with_inner(error)))?;
                        Ok(Value::Void)
                    }
                    Fun::Getchar => {
                        let mut buf = [0u8];
                        Ok(Value::String(
                            if std::io::stdin()
                                .read(&mut buf[..])
                                .map_err(|error| Error::IOError(name.with_inner(error)))?
                                == 0
                            {
                                Cow::Borrowed("")
                            } else {
                                Cow::Owned(String::from(char::from(buf[0])))
                            },
                        ))
                    }
                    Fun::Ord => Ok(Value::Integer(
                        self.eval(args.next().unwrap())?
                            .as_string()
                            .bytes()
                            .next()
                            .map(isize::from)
                            .unwrap_or(-1),
                    )),
                    Fun::Chr => Ok(Value::String(Cow::Owned(String::from(char::from(
                        u8::try_from(self.eval(args.next().unwrap())?.as_int())
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?,
                    ))))),
                    Fun::Size => Ok(Value::Integer(
                        self.eval(args.next().unwrap())?
                            .as_string()
                            .len()
                            .try_into()
                            .map_err(|error| Error::TryFromIntError(name.with_inner(error)))?,
                    )),
                    Fun::Substring => {
                        let s = self.eval(args.next().unwrap())?.as_string();
                        let first = self.eval_with_pos(args.next().unwrap())?.as_index()?;
                        let n = self.eval_with_pos(args.next().unwrap())?.as_index()?;
                        Ok(Value::String(Cow::Owned((&s[first..first + n]).into())))
                    }
                    Fun::Concat => {
                        let mut s1 = self.eval(args.next().unwrap())?.as_string().to_string();
                        let s2 = self.eval(args.next().unwrap())?.as_string();
                        s1.push_str(&s2);
                        Ok(Value::String(Cow::Owned(s1)))
                    }
                    Fun::Not => Ok(Value::Integer(
                        (self.eval(args.next().unwrap())?.as_int() == 0) as isize,
                    )),
                    Fun::Exit => {
                        std::process::exit(self.eval(args.next().unwrap())?.as_int() as i32)
                    }
                    Fun::Other { fields, body } => {
                        for (field, arg) in fields.iter().zip(args) {
                            let value = self.eval(arg)?;
                            self.venv.insert(field, value);
                        }
                        let ret = self.eval(&body);
                        for name in fields.iter() {
                            self.venv.remove(name);
                        }
                        ret
                    }
                }
            }
            Expr::Rec { fields, .. } => {
                let mut rec = HashMap::new();
                for (field, expr) in fields {
                    rec.insert(**field, self.eval(expr)?);
                }
                Ok(Value::Rec(Rc::new(rec)))
            }
            Expr::Array { n, v, .. } => {
                let n = self.eval_with_pos(n)?.as_index()?;
                let v = self.eval(v)?;
                Ok(Value::Array(Rc::new(once(v).cycle().take(n).collect())))
            }
            Expr::Assign(lvalue, expr) => {
                *self.eval_lvalue(lvalue)? = self.eval(expr)?;
                Ok(Value::Void)
            }
            Expr::Lvalue(lvalue) => self.eval_lvalue(lvalue).cloned(),
        }
    }

    fn eval_with_pos(&mut self, expr: &WithPos<Expr<'a>>) -> Result<WithPos<Value<'a>>, Error> {
        Ok(expr.with_inner(self.eval(expr)?))
    }
}

pub fn eval<'a>(expr: &'a Expr) -> Result<Value<'a>, Error> {
    Interpreter::new().eval(expr)
}
