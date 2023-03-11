use crate::ast::{self, Dec, Expr, Lvalue, Op};
use anyhow::Result;
use std::{
    collections::{HashMap, HashSet, LinkedList},
    fmt::{Debug, Display},
    rc::Rc,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TypeError {
    #[error("unsupported operand type(s) for {op}: {lty} and {rty}")]
    UnsupportedOperandType { op: Op, lty: RcType, rty: RcType },
    #[error("mismatched types: expected {expected}, found {found}")]
    MismatchedTypes { expected: RcType, found: RcType },
    #[error("{name} takes {expected} positional argument(s) but {found} were given")]
    MismatchedArgumentNum {
        name: String,
        expected: usize,
        found: usize,
    },
    #[error("recursive type found: {0}")]
    RecursiveType(String),
    #[error("unknown type of {0}")]
    UnknownType(String),
    #[error("name {0} is not defined")]
    NotDefined(String),
    #[error("{0} is not callable")]
    NotCallable(String),
    #[error("{0} is not record")]
    NotRecord(String),
    #[error("record has no field {0}")]
    NoSuchField(String),
    #[error("{0} is not array")]
    NotArray(String),
    #[error("break outside loop")]
    BreakOutsideLoop,
}

#[derive(Clone, Debug)]
pub struct RcType(Rc<Type>);

impl Display for RcType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<Type> for RcType {
    fn from(value: Type) -> Self {
        Self(Rc::new(value))
    }
}

impl std::ops::Deref for RcType {
    type Target = Type;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl PartialEq for RcType {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl RcType {
    fn expect(&self, expected: &RcType) -> Result<(), TypeError> {
        if self == expected {
            Ok(())
        } else {
            match (&**self, &**expected) {
                (Type::Array { .. }, Type::Nil)
                | (Type::Rec { .. }, Type::Nil)
                | (Type::Nil, Type::Rec { .. })
                | (Type::Nil, Type::Array { .. }) => Ok(()),
                _ => Err(TypeError::MismatchedTypes {
                    expected: expected.clone(),
                    found: self.clone(),
                }),
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Unknown(String),
    Void,
    Integer,
    String,
    Nil,
    Array {
        name: String,
        ty: RcType,
    },
    Rec {
        name: String,
        fields: HashMap<String, RcType>,
    },
    Fn {
        fields: Vec<RcType>,
        retty: RcType,
    },
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown(ty) => write!(f, "{}", ty),
            Self::Void => write!(f, "void"),
            Self::Integer => write!(f, "int"),
            Self::String => write!(f, "string"),
            Self::Nil => write!(f, "nil"),
            Self::Fn { .. } => write!(f, "function"),
            Self::Array { name, .. } => write!(f, "{}", name),
            Self::Rec { name, .. } => write!(f, "{}", name),
        }
    }
}

#[derive(Default)]
struct Env(HashMap<String, LinkedList<RcType>>);

impl Env {
    fn insert(&mut self, name: String, ty: RcType) {
        self.0.entry(name).or_default().push_front(ty);
    }

    fn remove(&mut self, name: &String) -> Option<RcType> {
        let tys = self.0.get_mut(name)?;
        let ty = tys.pop_front().unwrap();
        if tys.is_empty() {
            self.0.remove(name);
        }
        Some(ty)
    }

    fn get(&self, name: &String) -> Option<&RcType> {
        self.0.get(name).map(|tys| tys.front().unwrap())
    }

    fn get_ok(&self, name: &String) -> Result<&RcType, TypeError> {
        self.get(name)
            .ok_or_else(|| TypeError::NotDefined(name.clone()))
    }
}

struct Checker {
    tenv: Env,
    venv: Env,
    int: RcType,
    string: RcType,
    nil: RcType,
    void: RcType,
}

impl Checker {
    fn new() -> Self {
        let mut c = Self {
            tenv: Env::default(),
            venv: Env::default(),
            int: Type::Integer.into(),
            string: Type::String.into(),
            nil: Type::Nil.into(),
            void: Type::Void.into(),
        };

        c.tenv.insert("int".into(), c.int.clone());
        c.tenv.insert("string".into(), c.string.clone());

        macro_rules! func {
            ( $name:expr, ( $( $param:ident ),* ) => $retty:ident ) => {
                c.venv.insert(
                    stringify!($name).into(),
                    Type::Fn {
                        fields: Vec::from([$(c.$param.clone()),*]),
                        retty: c.$retty.clone(),
                    }
                    .into(),
                )
            };
        }
        func!(print, (string) => void);
        func!(flush, () => void);
        func!(getchar, () => string);
        func!(ord, (string) => int);
        func!(chr, (int) => string);
        func!(size, (string) => int);
        func!(substring, (string, int, int) => string);
        func!(concat, (string, string) => string);
        func!(not, (int) => int);
        func!(exit, (int) => void);

        c
    }

    fn resolve_lvalue(&mut self, lvalue: &Lvalue, breakable: bool) -> Result<RcType, TypeError> {
        match lvalue {
            Lvalue::Var(var) => Ok(self.venv.get_ok(var)?.clone()),
            Lvalue::Rec(var, field) => match &*self.resolve_lvalue(var, breakable)? {
                Type::Rec { fields, .. } => Ok(fields
                    .get(field)
                    .ok_or_else(|| TypeError::NoSuchField(field.clone()))?
                    .clone()),
                _ => Err(TypeError::NotRecord(format!("{}", var))),
            },
            Lvalue::Idx(var, idx) => match &*self.resolve_lvalue(var, breakable)? {
                Type::Array { ty, .. } => {
                    self.resolve(idx, breakable)?.expect(&self.int)?;
                    Ok(ty.clone())
                }
                _ => Err(TypeError::NotArray(format!("{}", var))),
            },
        }
    }

    fn try_resolve_tydec(&mut self, decs: &Vec<Dec>) -> Result<(), TypeError> {
        for dec in decs {
            if let Dec::TyDec(name, ty) = dec {
                let resolve = |ty: &String| {
                    self.tenv
                        .get(ty)
                        .cloned()
                        .unwrap_or_else(|| Type::Unknown(ty.clone()).into())
                };
                self.tenv.insert(
                    name.clone(),
                    match ty {
                        ast::Type::Type(ty) => resolve(ty),
                        ast::Type::Array(ty) => Type::Array {
                            name: name.clone(),
                            ty: resolve(ty),
                        }
                        .into(),
                        ast::Type::Rec(fields) => Type::Rec {
                            name: name.clone(),
                            fields: fields
                                .iter()
                                .map(|field| (field.name.clone(), resolve(&field.ty)))
                                .collect(),
                        }
                        .into(),
                    },
                );
            }
        }
        Ok(())
    }

    fn resolve_alias(&mut self) -> Result<(), TypeError> {
        let mut traces: HashMap<_, HashSet<_>> = HashMap::new();
        'a: loop {
            for (name, tys) in &self.tenv.0 {
                if let Type::Unknown(ty) = &**tys.front().unwrap() {
                    if !traces.entry(name.clone()).or_default().insert(ty.clone()) {
                        return Err(TypeError::RecursiveType(ty.clone()));
                    } else if let Some(ty) = self.tenv.get(ty).cloned() {
                        let name = name.clone();
                        self.tenv.remove(&name);
                        self.tenv.insert(name, ty);
                    }
                    continue 'a;
                }
            }
            break;
        }
        Ok(())
    }

    fn resolve_tydec(&mut self) -> Result<(), TypeError> {
        for tys in self.tenv.0.values() {
            let mut ty = tys.front().unwrap().clone();
            let resolve = |ty: &String| {
                self.tenv
                    .get(ty)
                    .cloned()
                    .ok_or_else(|| TypeError::NotDefined(ty.clone()))
            };
            match unsafe { Rc::get_mut_unchecked(&mut ty.0) } {
                Type::Array { ref mut ty, .. } => {
                    if let Type::Unknown(t) = &**ty {
                        *ty = resolve(t)?;
                    }
                }
                Type::Rec { ref mut fields, .. } => {
                    for ty in fields.values_mut() {
                        if let Type::Unknown(t) = &**ty {
                            *ty = resolve(t)?;
                        }
                    }
                }
                Type::Unknown(_) => unreachable!(),
                Type::Fn { .. } => unreachable!(),
                _ => (),
            }
        }
        Ok(())
    }

    fn resolve_vardec(&mut self, decs: &Vec<Dec>, breakable: bool) -> Result<(), TypeError> {
        for dec in decs {
            match dec {
                Dec::VarDec { name, ty, val } => {
                    let found = self.resolve(val, breakable)?;
                    match ty {
                        Some(ty) => {
                            let expected = self.tenv.get_ok(ty)?;
                            found.expect(expected)?;
                            self.venv.insert(name.clone(), expected.clone());
                        }
                        _ => {
                            if *found == Type::Nil {
                                return Err(TypeError::UnknownType(name.clone()));
                            } else {
                                self.venv.insert(name.clone(), found);
                            }
                        }
                    }
                }
                Dec::FnDec {
                    name,
                    fields,
                    retty,
                    ..
                } => {
                    self.venv.insert(
                        name.clone(),
                        Type::Fn {
                            fields: fields
                                .iter()
                                .map(|field| self.tenv.get_ok(&field.ty).cloned())
                                .try_collect()?,
                            retty: match retty {
                                Some(retty) => self.tenv.get_ok(retty)?.clone(),
                                None => self.void.clone(),
                            },
                        }
                        .into(),
                    );
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn resolve_fn_body(&mut self, decs: &Vec<Dec>) -> Result<(), TypeError> {
        for dec in decs {
            if let Dec::FnDec {
                fields,
                retty,
                body,
                ..
            } = dec
            {
                for field in fields {
                    self.venv
                        .insert(field.name.clone(), self.tenv.get_ok(&field.ty)?.clone());
                }
                self.resolve(body, false)?.expect(match retty {
                    Some(retty) => self.tenv.get_ok(retty)?,
                    None => &self.void,
                })?;
                for field in fields {
                    self.venv.remove(&field.name);
                }
            }
        }
        Ok(())
    }

    fn resolve(&mut self, expr: &Expr, breakable: bool) -> Result<RcType, TypeError> {
        match expr {
            Expr::BinOp { lhs, op, rhs } => {
                let lty = self.resolve(lhs, breakable)?;
                let rty = self.resolve(rhs, breakable)?;
                match (op, &*lty.0, &*rty.0) {
                    (
                        Op::Gt | Op::Ge | Op::Lt | Op::Le | Op::Ne | Op::Eq,
                        Type::String,
                        Type::String,
                    )
                    | (_, Type::Integer, Type::Integer)
                    | (Op::Ne | Op::Eq, Type::Array { .. }, Type::Array { .. })
                    | (Op::Ne | Op::Eq, Type::Array { .. }, Type::Nil)
                    | (Op::Ne | Op::Eq, Type::Nil, Type::Array { .. })
                    | (Op::Ne | Op::Eq, Type::Rec { .. }, Type::Rec { .. })
                    | (Op::Ne | Op::Eq, Type::Rec { .. }, Type::Nil)
                    | (Op::Ne | Op::Eq, Type::Nil, Type::Rec { .. }) => Ok(self.int.clone()),
                    _ => Err(TypeError::UnsupportedOperandType { op: *op, lty, rty }),
                }
            }
            Expr::Nil => Ok(self.nil.clone()),
            Expr::Neg(expr) => {
                self.resolve(expr, breakable)?.expect(&self.int)?;
                Ok(self.int.clone())
            }
            Expr::Seq(exprs) => match &exprs[..] {
                [] => Ok(self.nil.clone()),
                [exprs @ .., expr] => {
                    for expr in exprs {
                        self.resolve(expr, breakable)?;
                    }
                    self.resolve(expr, breakable)
                }
            },
            Expr::Integer(_) => Ok(self.int.clone()),
            Expr::String(_) => Ok(self.string.clone()),
            Expr::If(cond, t, f) => {
                self.resolve(cond, breakable)?.expect(&self.int)?;
                match f {
                    Some(f) => {
                        let tty = self.resolve(t, breakable)?;
                        let fty = self.resolve(f, breakable)?;
                        tty.expect(&fty)?;
                        Ok(tty)
                    }
                    None => {
                        self.resolve(t, breakable)?.expect(&self.void)?;
                        Ok(self.void.clone())
                    }
                }
            }
            Expr::While(cond, body) => {
                self.resolve(cond, breakable)?.expect(&self.int)?;
                self.resolve(body, breakable)?.expect(&self.void)?;
                Ok(self.void.clone())
            }
            Expr::For(name, begin, end, body) => {
                self.resolve(begin, breakable)?.expect(&self.int)?;
                self.resolve(end, breakable)?.expect(&self.int)?;
                self.venv.insert(name.clone(), self.int.clone());
                self.resolve(body, true)?;
                self.venv.remove(name);
                Ok(self.void.clone())
            }
            Expr::Break => {
                if breakable {
                    Ok(self.void.clone())
                } else {
                    Err(TypeError::BreakOutsideLoop)
                }
            }
            Expr::Let(decs, expr) => {
                self.try_resolve_tydec(decs)?;
                self.resolve_alias()?;
                self.resolve_tydec()?;
                self.resolve_vardec(decs, breakable)?;
                self.resolve_fn_body(decs)?;
                self.resolve(expr, breakable)
            }
            Expr::FnCall { name, args } => {
                let ty = self.venv.get_ok(name)?.clone();
                match &*ty {
                    Type::Fn { fields, retty } => {
                        if fields.len() != args.len() {
                            return Err(TypeError::MismatchedArgumentNum {
                                name: name.clone(),
                                expected: fields.len(),
                                found: args.len(),
                            });
                        }
                        for (param, arg) in fields.iter().zip(args) {
                            self.resolve(arg, breakable)?.expect(param)?;
                        }
                        Ok(retty.clone())
                    }
                    _ => Err(TypeError::NotCallable(name.clone())),
                }
            }
            Expr::Rec { ty, fields } => {
                let t = self.tenv.get_ok(ty)?.clone();
                match &*t {
                    Type::Rec { fields: fs, .. } => {
                        for (name, val) in fields {
                            self.resolve(val, breakable)?.expect(
                                fs.get(name)
                                    .ok_or_else(|| TypeError::NoSuchField(name.clone()))?,
                            )?;
                        }
                        Ok(t)
                    }
                    _ => Err(TypeError::NotRecord(ty.clone())),
                }
            }
            Expr::Array { ty, n, v } => {
                self.resolve(n, breakable)?.expect(&self.int)?;
                let t = self.tenv.get_ok(ty)?.clone();
                match &*t {
                    Type::Array { ty, .. } => {
                        self.resolve(v, breakable)?.expect(ty)?;
                        Ok(t)
                    }
                    _ => Err(TypeError::NotArray(ty.clone())),
                }
            }
            Expr::Assign(lvalue, expr) => {
                self.resolve(expr, breakable)?
                    .expect(&self.resolve_lvalue(lvalue, breakable)?)?;
                Ok(self.void.clone())
            }
            Expr::Lvalue(lvalue) => self.resolve_lvalue(lvalue, breakable),
        }
    }
}

pub fn check(expr: &Expr) -> Result<(), TypeError> {
    Checker::new().resolve(expr, false)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use anyhow::anyhow;
    use std::{collections::HashSet, fs};
    use test::Bencher;

    #[test]
    fn test_samples() -> Result<()> {
        let errors = HashSet::from([
            "test9.tig",
            "test10.tig",
            "test11.tig",
            "test13.tig",
            "test14.tig",
            "test15.tig",
            "test16.tig",
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
        ]);
        for sample in fs::read_dir("samples")? {
            let sample = sample?;
            if sample.file_name() != "test49.tig" {
                let result = check(&parse(&fs::read_to_string(sample.path())?)?);
                if errors.contains(sample.file_name().to_str().unwrap()) {
                    assert!(result.is_err());
                } else if let Err(error) = result {
                    return Err(anyhow!("Check {:?}: {}", sample.file_name(), error));
                }
            }
        }
        Ok(())
    }

    #[bench]
    fn bench_samples(b: &mut Bencher) -> Result<()> {
        let samples: Vec<_> = fs::read_dir("samples")?
            .into_iter()
            .map(|sample| fs::read_to_string(sample?.path()))
            .try_collect::<Vec<_>>()?
            .into_iter()
            .filter_map(|sample| parse(&sample).ok())
            .collect();
        b.iter(|| {
            for sample in &samples {
                _ = check(sample);
            }
        });
        Ok(())
    }
}
