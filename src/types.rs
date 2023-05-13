use crate::{
    ast::{self, Dec, Expr, Lvalue, Op, WithPos},
    env::Env,
    error::Error,
};
use anyhow::Result;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    rc::Rc,
};

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
    fn expect(&self, expected: &RcType) -> Result<(), Error> {
        if &**self == expected {
            Ok(())
        } else {
            match (&***self, &**expected) {
                (Type::Array { .. }, Type::Nil)
                | (Type::Rec { .. }, Type::Nil)
                | (Type::Nil, Type::Rec { .. })
                | (Type::Nil, Type::Array { .. }) => Ok(()),
                _ => Err(Error::MismatchedTypes {
                    expected: expected.to_string(),
                    found: self.with_inner(self.inner.to_string()),
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
        lvalue: &WithPos<Lvalue<'a>>,
        breakable: bool,
    ) -> Result<RcType, Error> {
        match &**lvalue {
            Lvalue::Var(var) => Ok(self.venv.get(var)?.clone()),
            Lvalue::Rec(var, field) => match &*self.resolve_lvalue(var, breakable)? {
                Type::Rec { fields, .. } => Ok(fields
                    .get(**field)
                    .ok_or_else(|| Error::NoSuchField(field.into()))?
                    .clone()),
                _ => Err(Error::NotRecord(lvalue.with_inner(var.to_string()))),
            },
            Lvalue::Idx(var, index) => match &*self.resolve_lvalue(var, breakable)? {
                Type::Array { ty, .. } => {
                    self.resolve_with_pos(index, breakable)?.expect(&self.int)?;
                    Ok(ty.clone())
                }
                _ => Err(Error::NotArray(lvalue.with_inner(var.to_string()))),
            },
        }
    }

    fn try_resolve_tydec(&mut self, decs: &Vec<Dec<'a>>) -> Result<Vec<String>, Error> {
        let mut tnames = Vec::new();
        for dec in decs {
            if let Dec::TyDec(name, ty) = dec {
                tnames.push(name.to_string());
                let resolve = |ty| {
                    self.tenv
                        .get(ty)
                        .cloned()
                        .unwrap_or_else(|_| Type::Unknown(ty.into()).into())
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
        Ok(tnames)
    }

    fn resolve_alias(&mut self) -> Result<(), Error> {
        let mut traces: HashMap<_, HashSet<_>> = HashMap::new();
        'a: loop {
            for (name, tys) in &self.tenv.0 {
                if let Type::Unknown(ty) = &**tys.front().unwrap() {
                    if !traces.entry(*name).or_default().insert(ty.inner.clone()) {
                        return Err(Error::RecursiveType(ty.clone()));
                    } else if let Ok(ty) = self.tenv.gets(ty).cloned() {
                        let name = *name;
                        self.tenv.remove(name);
                        self.tenv.insert(name, ty);
                    }
                    continue 'a;
                }
            }
            break;
        }
        Ok(())
    }

    fn resolve_tydec(&mut self) -> Result<(), Error> {
        for tys in self.tenv.0.values() {
            let mut ty = tys.front().unwrap().clone();
            let resolve = |ty: &WithPos<String>| self.tenv.gets(ty).cloned();
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
    ) -> Result<(Vec<String>, Vec<String>), Error> {
        let mut vnames = Vec::new();
        let mut fnames = Vec::new();
        for dec in decs {
            match dec {
                Dec::VarDec { name, ty, val } => {
                    vnames.push(name.to_string());
                    let found = self.resolve_with_pos(val, breakable)?;
                    match ty {
                        Some(ty) => {
                            let expected = self.tenv.get(ty)?;
                            found.expect(expected)?;
                            self.venv.insert(name, expected.clone());
                        }
                        _ => {
                            if *found.inner == Type::Nil {
                                return Err(Error::UnknownType(name.into()));
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
                    fnames.push(name.to_string());
                    self.venv.insert(
                        name,
                        Type::Fn {
                            fields: fields
                                .iter()
                                .map(|field| self.tenv.get(&field.ty).cloned())
                                .try_collect()?,
                            retty: match retty {
                                Some(retty) => self.tenv.get(retty)?.clone(),
                                None => self.void.clone(),
                            },
                        }
                        .into(),
                    );
                }
                _ => (),
            }
        }
        Ok((vnames, fnames))
    }

    fn resolve_fn_body(&mut self, decs: &Vec<Dec<'a>>) -> Result<(), Error> {
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
                        .insert(field.name, self.tenv.get(&field.ty)?.clone());
                }
                self.resolve_with_pos(body, false)?.expect(match retty {
                    Some(retty) => self.tenv.get(retty)?,
                    None => &self.void,
                })?;
                for field in fields {
                    self.venv.remove(field.name);
                }
            }
        }
        Ok(())
    }

    fn resolve(&mut self, expr: &Expr<'a>, breakable: bool) -> Result<RcType, Error> {
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
                    _ => Err(Error::UnsupportedOperandType {
                        op: *op,
                        lty: lty.to_string(),
                        rty: rty.to_string(),
                    }),
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
                    Err(Error::BreakOutsideLoop(*pos))
                }
            }
            Expr::Let(decs, expr) => {
                let tnames = self.try_resolve_tydec(decs)?;
                self.resolve_alias()?;
                self.resolve_tydec()?;
                let (vnames, fnames) = self.resolve_vardec(decs, breakable)?;
                self.resolve_fn_body(decs)?;
                let val = self.resolve(expr, breakable);
                for tname in tnames {
                    self.tenv.remove(&tname);
                }
                for vname in vnames {
                    self.venv.remove(&vname);
                }
                for fname in fnames {
                    self.venv.remove(&fname);
                }
                val
            }
            Expr::FnCall { name, args } => {
                let ty = self.venv.get(name)?.clone();
                match &*ty {
                    Type::Fn { fields, retty } => {
                        if fields.len() != args.len() {
                            return Err(Error::MismatchedArgumentNum {
                                name: name.into(),
                                expected: fields.len(),
                                found: args.len(),
                            });
                        }
                        for (param, arg) in fields.iter().zip(args) {
                            self.resolve_with_pos(arg, breakable)?.expect(param)?;
                        }
                        Ok(retty.clone())
                    }
                    _ => Err(Error::NotCallable(name.into())),
                }
            }
            Expr::Rec { ty, fields } => {
                let t = self.tenv.get(ty)?.clone();
                match &*t {
                    Type::Rec { fields: fs, .. } => {
                        for (name, val) in fields {
                            let expected = fs
                                .get(**name)
                                .ok_or_else(|| Error::NoSuchField(name.into()))?;
                            self.resolve_with_pos(val, breakable)?.expect(expected)?;
                        }
                        Ok(t)
                    }
                    _ => Err(Error::NotRecord(ty.into())),
                }
            }
            Expr::Array { ty, n, v } => {
                self.resolve_with_pos(n, breakable)?.expect(&self.int)?;
                let t = self.tenv.get(ty)?.clone();
                match &*t {
                    Type::Array { ty, .. } => {
                        self.resolve_with_pos(v, breakable)?.expect(ty)?;
                        Ok(t)
                    }
                    _ => Err(Error::NotArray(ty.into())),
                }
            }
            Expr::Assign(lvalue, expr) => {
                let expected = &self.resolve_lvalue(lvalue, breakable)?;
                self.resolve_with_pos(expr, breakable)?.expect(expected)?;
                Ok(self.void.clone())
            }
            Expr::Lvalue(lvalue) => self.resolve_lvalue(lvalue, breakable),
        }
    }

    fn resolve_with_pos(
        &mut self,
        expr: &WithPos<Expr<'a>>,
        breakable: bool,
    ) -> Result<WithPos<RcType>, Error> {
        Ok(expr.with_inner(self.resolve(expr, breakable)?))
    }
}

pub fn check<'a>(expr: &Expr<'a>) -> Result<(), Error> {
    Checker::new().resolve(expr, false)?;
    Ok(())
}
