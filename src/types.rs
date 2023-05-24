use crate::{
    ast::{self, Dec, Expr, Lvalue, Op, WithPos},
    env::Env,
    error::Error,
};
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

#[derive(Debug, Clone)]
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
    Fun {
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
            Self::Fun { .. } => "function",
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

        macro_rules! fun {
            ( $name:expr, ( $( $param:ident ),* ) => $retty:ident ) => {
                c.venv.insert(
                    stringify!($name).into(),
                    Type::Fun {
                        fields: Vec::from([$(c.$param.clone()),*]),
                        retty: c.$retty.clone(),
                    }
                    .into(),
                )
            };
        }
        fun!(print, (string) => void);
        fun!(flush, () => void);
        fun!(getchar, () => string);
        fun!(ord, (string) => int);
        fun!(chr, (int) => string);
        fun!(size, (string) => int);
        fun!(substring, (string, int, int) => string);
        fun!(concat, (string, string) => string);
        fun!(not, (int) => int);
        fun!(exit, (int) => void);

        c
    }

    fn check_lvalue(
        &mut self,
        lvalue: &WithPos<Lvalue<'a>>,
        breakable: bool,
    ) -> Result<RcType, Error> {
        match &**lvalue {
            Lvalue::Var(var) => Ok(self.venv.get(var)?.clone()),
            Lvalue::Rec(lvalue, field) => match &*self.check_lvalue(lvalue, breakable)? {
                Type::Rec { fields, .. } => Ok(fields
                    .get(**field)
                    .ok_or_else(|| Error::NoSuchField(field.into()))?
                    .clone()),
                _ => Err(Error::NotRecord(lvalue.with_inner(lvalue.to_string()))),
            },
            Lvalue::Idx(lvalue, index) => match &*self.check_lvalue(lvalue, breakable)? {
                Type::Array { ty, .. } => {
                    self.check_with_pos(index, breakable)?.expect(&self.int)?;
                    Ok(ty.clone())
                }
                _ => Err(Error::NotArray(lvalue.with_inner(lvalue.to_string()))),
            },
        }
    }

    fn try_check_tydec(&mut self, decs: &Vec<Dec<'a>>) -> Result<(), Error> {
        for dec in decs {
            if let Dec::TyDec { name, ty } = dec {
                let get = |ty: &WithPos<&str>| {
                    self.tenv
                        .get(ty)
                        .cloned()
                        .unwrap_or_else(|_| Type::Unknown(ty.into()).into())
                };
                self.tenv.insert(
                    name,
                    match &**ty {
                        ast::Type::Type(ty) => get(ty),
                        ast::Type::Array(ty) => Type::Array {
                            name: name.to_string(),
                            ty: get(ty),
                        }
                        .into(),
                        ast::Type::Rec(fields) => Type::Rec {
                            name: name.to_string(),
                            fields: fields
                                .iter()
                                .map(|field| (field.name.into(), get(&field.ty)))
                                .collect(),
                        }
                        .into(),
                    },
                );
            }
        }
        Ok(())
    }

    fn check_alias(&mut self) -> Result<(), Error> {
        let mut traces: HashMap<_, HashSet<_>> = HashMap::new();
        'a: loop {
            for (&name, tys) in &self.tenv.0 {
                if let Type::Unknown(ty) = &**tys.front().unwrap() {
                    if !traces.entry(name).or_default().insert(ty.inner.clone()) {
                        return Err(Error::RecursiveType(ty.clone()));
                    } else if let Ok(ty) = self.tenv.get(ty).cloned() {
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

    fn check_tydec(&mut self) -> Result<(), Error> {
        for tys in self.tenv.0.values() {
            let mut ty = tys.front().unwrap().clone();
            let get = |ty: &WithPos<String>| self.tenv.get(ty).cloned();
            match unsafe { Rc::get_mut_unchecked(&mut ty.0) } {
                Type::Array { ref mut ty, .. } => {
                    if let Type::Unknown(t) = &**ty {
                        *ty = get(t)?;
                    }
                }
                Type::Rec { ref mut fields, .. } => {
                    for ty in fields.values_mut() {
                        if let Type::Unknown(t) = &**ty {
                            *ty = get(t)?;
                        }
                    }
                }
                Type::Unknown(_) => unreachable!(),
                Type::Fun { .. } => unreachable!(),
                _ => (),
            }
        }
        Ok(())
    }

    fn check_vardec(&mut self, decs: &Vec<Dec<'a>>, breakable: bool) -> Result<(), Error> {
        for dec in decs {
            match dec {
                Dec::VarDec { name, ty, expr } => {
                    let found = self.check_with_pos(expr, breakable)?;
                    match ty {
                        Some(ty) => {
                            let expected = self.tenv.get(ty)?;
                            found.expect(expected)?;
                            self.venv.insert(name, expected.clone());
                        }
                        _ => match **found {
                            Type::Nil => return Err(Error::UnknownType(name.into())),
                            _ => self.venv.insert(name, found.inner),
                        },
                    }
                }
                Dec::FunDec {
                    name,
                    fields,
                    retty,
                    ..
                } => {
                    self.venv.insert(
                        name,
                        Type::Fun {
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
        Ok(())
    }

    fn check_funbody(&mut self, decs: &Vec<Dec<'a>>) -> Result<(), Error> {
        for dec in decs {
            if let Dec::FunDec {
                fields,
                retty,
                body,
                ..
            } = dec
            {
                for field in fields {
                    let ty = self.tenv.get(&field.ty)?.clone();
                    self.venv.insert(field.name, ty);
                }
                self.check_with_pos(body, false)?.expect(match retty {
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

    fn check(&mut self, expr: &Expr<'a>, breakable: bool) -> Result<RcType, Error> {
        match expr {
            Expr::BinOp { lhs, op, rhs } => {
                let lty = self.check(lhs, breakable)?;
                let rty = self.check(rhs, breakable)?;
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
                self.check_with_pos(expr, breakable)?.expect(&self.int)?;
                Ok(self.int.clone())
            }
            Expr::Seq(exprs) => match &exprs[..] {
                [] => Ok(self.nil.clone()),
                [exprs @ .., expr] => {
                    for expr in exprs {
                        self.check(expr, breakable)?;
                    }
                    self.check(expr, breakable)
                }
            },
            Expr::Integer(_) => Ok(self.int.clone()),
            Expr::String(_) => Ok(self.string.clone()),
            Expr::If(cond, t, f) => {
                self.check_with_pos(cond, breakable)?.expect(&self.int)?;
                match f {
                    Some(f) => {
                        let tty = self.check(t, breakable)?;
                        let fty = self.check_with_pos(f, breakable)?;
                        fty.expect(&tty)?;
                        Ok(match &*tty {
                            Type::Nil => fty.inner,
                            _ => tty,
                        })
                    }
                    None => {
                        self.check_with_pos(t, breakable)?.expect(&self.void)?;
                        Ok(self.void.clone())
                    }
                }
            }
            Expr::While(cond, body) => {
                self.check_with_pos(cond, breakable)?.expect(&self.int)?;
                self.check_with_pos(body, breakable)?.expect(&self.void)?;
                Ok(self.void.clone())
            }
            Expr::For(name, begin, end, body) => {
                self.check_with_pos(begin, breakable)?.expect(&self.int)?;
                self.check_with_pos(end, breakable)?.expect(&self.int)?;
                self.venv.insert(name, self.int.clone());
                self.check(body, true)?;
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
                self.try_check_tydec(decs)?;
                self.check_alias()?;
                self.check_tydec()?;
                self.check_vardec(decs, breakable)?;
                self.check_funbody(decs)?;
                let ty = self.check(expr, breakable);
                for dec in decs {
                    match dec {
                        Dec::TyDec { name, .. } => self.tenv.remove(name),
                        Dec::VarDec { name, .. } => self.venv.remove(name),
                        Dec::FunDec { name, .. } => self.venv.remove(name),
                    };
                }
                ty
            }
            Expr::FunCall { name, args } => {
                let ty = self.venv.get(name)?.clone();
                match &*ty {
                    Type::Fun { fields, retty } => {
                        if fields.len() != args.len() {
                            return Err(Error::MismatchedArgumentNum {
                                name: name.into(),
                                expected: fields.len(),
                                found: args.len(),
                            });
                        }
                        for (param, arg) in fields.iter().zip(args) {
                            self.check_with_pos(arg, breakable)?.expect(param)?;
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
                        for (name, expr) in fields {
                            let expected = fs
                                .get(**name)
                                .ok_or_else(|| Error::NoSuchField(name.into()))?;
                            self.check_with_pos(expr, breakable)?.expect(expected)?;
                        }
                        Ok(t)
                    }
                    _ => Err(Error::NotRecord(ty.into())),
                }
            }
            Expr::Array { ty, n, v } => {
                self.check_with_pos(n, breakable)?.expect(&self.int)?;
                let t = self.tenv.get(ty)?.clone();
                match &*t {
                    Type::Array { ty, .. } => {
                        self.check_with_pos(v, breakable)?.expect(ty)?;
                        Ok(t)
                    }
                    _ => Err(Error::NotArray(ty.into())),
                }
            }
            Expr::Assign(lvalue, expr) => {
                let expected = &self.check_lvalue(lvalue, breakable)?;
                self.check_with_pos(expr, breakable)?.expect(expected)?;
                Ok(self.void.clone())
            }
            Expr::Lvalue(lvalue) => self.check_lvalue(lvalue, breakable),
        }
    }

    fn check_with_pos(
        &mut self,
        expr: &WithPos<Expr<'a>>,
        breakable: bool,
    ) -> Result<WithPos<RcType>, Error> {
        Ok(expr.with_inner(self.check(expr, breakable)?))
    }
}

pub fn check<'a>(expr: &Expr<'a>) -> Result<(), Error> {
    Checker::new().check(expr, false)?;
    Ok(())
}
