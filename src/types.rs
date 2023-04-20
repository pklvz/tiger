use crate::{
    ast::{self, Dec, Expr, Lvalue, Op, Pos, WithPos},
    env::Env,
};
use anyhow::Result;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    rc::Rc,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TypeError<'a> {
    #[error("{}, unsupported operand type(s) for {}: {lty} and {rty}", .op.pos, .op.inner)]
    UnsupportedOperandType {
        op: WithPos<Op>,
        lty: RcType,
        rty: RcType,
    },
    #[error("{}, mismatched types: expected {expected}, found {}", .found.pos, .found.inner)]
    MismatchedTypes {
        expected: RcType,
        found: WithPos<RcType>,
    },
    #[error("{}, {} takes {expected} positional argument(s) but {found} were given", .name.pos, .name.inner)]
    MismatchedArgumentNum {
        name: WithPos<&'a str>,
        expected: usize,
        found: usize,
    },
    #[error("{}, recursive type found: {}", .0.pos, .0.inner)]
    RecursiveType(WithPos<String>),
    #[error("{}, unknown type of {}", .0.pos, .0.inner)]
    UnknownType(WithPos<&'a str>),
    #[error("{}, name {} is not defined", .0.pos, .0.inner)]
    NotDefined(WithPos<String>),
    #[error("{}, {} is not callable", .0.pos, .0.inner)]
    NotCallable(WithPos<&'a str>),
    #[error("{}, {} is not record", .0.pos, .0.inner)]
    NotRecord(WithPos<String>),
    #[error("{}, record has no field {}", .0.pos, .0.inner)]
    NoSuchField(WithPos<&'a str>),
    #[error("{}, {} is not array", .0.pos, .0.inner)]
    NotArray(WithPos<String>),
    #[error("{0}, break outside loop")]
    BreakOutsideLoop(Pos),
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

impl WithPos<RcType> {
    fn expect<'a>(&self, expected: &RcType) -> Result<(), TypeError<'a>> {
        if &**self == expected {
            Ok(())
        } else {
            match (&***self, &**expected) {
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
    Unknown(WithPos<String>),
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
        f.write_str(match self {
            Self::Unknown(ty) => &ty.inner,
            Self::Void => "void",
            Self::Integer => "int",
            Self::String => "string",
            Self::Nil => "nil",
            Self::Fn { .. } => "function",
            Self::Array { name, .. } => name,
            Self::Rec { name, .. } => name,
        })
    }
}

struct Checker<'a> {
    tenv: Env<'a, RcType>,
    venv: Env<'a, RcType>,
    int: RcType,
    string: RcType,
    nil: RcType,
    void: RcType,
}

impl<'a> Checker<'a> {
    fn new() -> Self {
        let mut c = Self {
            tenv: Env::new(),
            venv: Env::new(),
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

    fn resolve_lvalue(
        &mut self,
        lvalue: &Lvalue<'a>,
        pos: Pos,
        breakable: bool,
    ) -> Result<RcType, TypeError<'a>> {
        match lvalue {
            Lvalue::Var(var) => Ok(self
                .venv
                .get(var)
                .ok_or_else(|| TypeError::NotDefined(var.into()))?
                .clone()),
            Lvalue::Rec(var, field) => match &*self.resolve_lvalue(var, pos, breakable)? {
                Type::Rec { fields, .. } => Ok(fields
                    .get(**field)
                    .ok_or_else(|| TypeError::NoSuchField(*field))?
                    .clone()),
                _ => Err(TypeError::NotRecord(WithPos {
                    inner: format!("{}", var),
                    pos,
                })),
            },
            Lvalue::Idx(var, idx) => match &*self.resolve_lvalue(var, pos, breakable)? {
                Type::Array { ty, .. } => {
                    self.resolve_with_pos(idx, breakable)?.expect(&self.int)?;
                    Ok(ty.clone())
                }
                _ => Err(TypeError::NotArray(WithPos {
                    inner: format!("{}", var),
                    pos,
                })),
            },
        }
    }

    fn try_resolve_tydec(&mut self, decs: &Vec<Dec<'a>>) -> Result<(), TypeError<'a>> {
        for dec in decs {
            if let Dec::TyDec(name, ty) = dec {
                let resolve = |ty: &WithPos<&str>| {
                    self.tenv
                        .get(ty)
                        .cloned()
                        .unwrap_or_else(|| Type::Unknown(ty.into()).into())
                };
                self.tenv.insert(
                    name,
                    match &**ty {
                        ast::Type::Type(ty) => resolve(ty),
                        ast::Type::Array(ty) => Type::Array {
                            name: name.to_string(),
                            ty: resolve(ty),
                        }
                        .into(),
                        ast::Type::Rec(fields) => Type::Rec {
                            name: name.to_string(),
                            fields: fields
                                .iter()
                                .map(|field| (field.name.to_string(), resolve(&field.ty)))
                                .collect(),
                        }
                        .into(),
                    },
                );
            }
        }
        Ok(())
    }

    fn resolve_alias(&mut self) -> Result<(), TypeError<'a>> {
        let mut traces: HashMap<_, HashSet<_>> = HashMap::new();
        'a: loop {
            for (name, tys) in &self.tenv.0 {
                if let Type::Unknown(ty) = &**tys.front().unwrap() {
                    if !traces
                        .entry(name.clone())
                        .or_default()
                        .insert(ty.inner.clone())
                    {
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

    fn resolve_tydec(&mut self) -> Result<(), TypeError<'a>> {
        for tys in self.tenv.0.values() {
            let mut ty = tys.front().unwrap().clone();
            let resolve = |ty: &WithPos<String>| {
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

    fn resolve_vardec(
        &mut self,
        decs: &Vec<Dec<'a>>,
        breakable: bool,
    ) -> Result<(), TypeError<'a>> {
        for dec in decs {
            match dec {
                Dec::VarDec { name, ty, val } => {
                    let found = self.resolve_with_pos(val, breakable)?;
                    match ty {
                        Some(ty) => {
                            let expected = self
                                .tenv
                                .get(ty)
                                .ok_or_else(|| TypeError::NotDefined(ty.into()))?;
                            found.expect(expected)?;
                            self.venv.insert(name, expected.clone());
                        }
                        _ => {
                            if *found.inner == Type::Nil {
                                return Err(TypeError::UnknownType(*name));
                            } else {
                                self.venv.insert(name, found.inner);
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
                        name,
                        Type::Fn {
                            fields: fields
                                .iter()
                                .map(|field| {
                                    self.tenv
                                        .get(&field.ty)
                                        .ok_or_else(|| TypeError::NotDefined(field.ty.into()))
                                        .cloned()
                                })
                                .try_collect()?,
                            retty: match retty {
                                Some(retty) => self
                                    .tenv
                                    .get(retty)
                                    .ok_or_else(|| TypeError::NotDefined(retty.into()))?
                                    .clone(),
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

    fn resolve_fn_body(&mut self, decs: &Vec<Dec<'a>>) -> Result<(), TypeError<'a>> {
        for dec in decs {
            if let Dec::FnDec {
                fields,
                retty,
                body,
                ..
            } = dec
            {
                for field in fields {
                    self.venv.insert(
                        field.name,
                        self.tenv
                            .get(&field.ty)
                            .ok_or_else(|| TypeError::NotDefined(field.ty.into()))?
                            .clone(),
                    );
                }
                self.resolve_with_pos(body, false)?.expect(match retty {
                    Some(retty) => self
                        .tenv
                        .get(retty)
                        .ok_or_else(|| TypeError::NotDefined(retty.into()))?,
                    None => &self.void,
                })?;
                for field in fields {
                    self.venv.remove(field.name);
                }
            }
        }
        Ok(())
    }

    fn resolve(&mut self, expr: &Expr<'a>, breakable: bool) -> Result<RcType, TypeError<'a>> {
        match expr {
            Expr::BinOp { lhs, op, rhs } => {
                let lty = self.resolve(lhs, breakable)?;
                let rty = self.resolve(rhs, breakable)?;
                match (&**op, &*lty.0, &*rty.0) {
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
                self.resolve_with_pos(expr, breakable)?.expect(&self.int)?;
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
                self.resolve_with_pos(cond, breakable)?.expect(&self.int)?;
                match f {
                    Some(f) => {
                        let tty = self.resolve(t, breakable)?;
                        let fty = self.resolve_with_pos(f, breakable)?;
                        fty.expect(&tty)?;
                        Ok(tty)
                    }
                    None => {
                        self.resolve_with_pos(t, breakable)?.expect(&self.void)?;
                        Ok(self.void.clone())
                    }
                }
            }
            Expr::While(cond, body) => {
                self.resolve_with_pos(cond, breakable)?.expect(&self.int)?;
                self.resolve_with_pos(body, breakable)?.expect(&self.void)?;
                Ok(self.void.clone())
            }
            Expr::For(name, begin, end, body) => {
                self.resolve_with_pos(begin, breakable)?.expect(&self.int)?;
                self.resolve_with_pos(end, breakable)?.expect(&self.int)?;
                self.venv.insert(name, self.int.clone());
                self.resolve(body, true)?;
                self.venv.remove(name);
                Ok(self.void.clone())
            }
            Expr::Break(pos) => {
                if breakable {
                    Ok(self.void.clone())
                } else {
                    Err(TypeError::BreakOutsideLoop(*pos))
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
                let ty = self
                    .venv
                    .get(name)
                    .ok_or_else(|| TypeError::NotDefined(name.into()))?
                    .clone();
                match &*ty {
                    Type::Fn { fields, retty } => {
                        if fields.len() != args.len() {
                            return Err(TypeError::MismatchedArgumentNum {
                                name: *name,
                                expected: fields.len(),
                                found: args.len(),
                            });
                        }
                        for (param, arg) in fields.iter().zip(args) {
                            self.resolve_with_pos(arg, breakable)?.expect(param)?;
                        }
                        Ok(retty.clone())
                    }
                    _ => Err(TypeError::NotCallable(*name)),
                }
            }
            Expr::Rec { ty, fields } => {
                let t = self
                    .tenv
                    .get(ty)
                    .ok_or_else(|| TypeError::NotDefined(ty.into()))?
                    .clone();
                match &*t {
                    Type::Rec { fields: fs, .. } => {
                        for (name, val) in fields {
                            self.resolve_with_pos(val, breakable)?.expect(
                                fs.get(**name)
                                    .ok_or_else(|| TypeError::NoSuchField(*name))?,
                            )?;
                        }
                        Ok(t)
                    }
                    _ => Err(TypeError::NotRecord(ty.into())),
                }
            }
            Expr::Array { ty, n, v } => {
                self.resolve_with_pos(n, breakable)?.expect(&self.int)?;
                let t = self
                    .tenv
                    .get(ty)
                    .ok_or_else(|| TypeError::NotDefined(ty.into()))?
                    .clone();
                match &*t {
                    Type::Array { ty, .. } => {
                        self.resolve_with_pos(v, breakable)?.expect(ty)?;
                        Ok(t)
                    }
                    _ => Err(TypeError::NotArray(ty.into())),
                }
            }
            Expr::Assign(lvalue, expr) => {
                self.resolve_with_pos(expr, breakable)?
                    .expect(&self.resolve_lvalue(lvalue, lvalue.pos, breakable)?)?;
                Ok(self.void.clone())
            }
            Expr::Lvalue(lvalue) => self.resolve_lvalue(lvalue, lvalue.pos, breakable),
        }
    }

    fn resolve_with_pos(
        &mut self,
        expr: &WithPos<Expr<'a>>,
        breakable: bool,
    ) -> Result<WithPos<RcType>, TypeError<'a>> {
        Ok(WithPos {
            inner: self.resolve(expr, breakable)?,
            pos: expr.pos,
        })
    }
}

pub fn check<'a>(expr: &Expr<'a>) -> Result<(), TypeError<'a>> {
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
                let ast = fs::read_to_string(sample.path())?;
                let result = check(&parse(&ast)?);
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
            .try_collect()?;
        let samples: Vec<_> = samples
            .iter()
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
