use std::cmp::max;
use std::collections::BTreeMap;

#[allow(dead_code)]
pub enum BinOp {
    Plus,
    Minus,
    Times,
    Div,
}

pub enum Exp {
    Id(String),
    Num(isize),
    Op(Box<Self>, BinOp, Box<Self>),
    Eseq(Box<Stm>, Box<Self>),
}

pub enum Stm {
    Compound(Box<Self>, Box<Self>),
    Assign { id: String, exp: Exp },
    Print(Vec<Exp>),
}

impl Exp {
    pub fn maxargs(&self) -> usize {
        match self {
            Exp::Op(lhs, _, rhs) => max(lhs.maxargs(), rhs.maxargs()),
            Exp::Eseq(stm, exp) => max(stm.maxargs(), exp.maxargs()),
            _ => 0,
        }
    }

    pub fn interp_exp(&self, table: &mut BTreeMap<String, isize>) -> isize {
        match self {
            Exp::Id(id) => table[id],
            Exp::Num(num) => *num,
            Exp::Op(lhs, op, rhs) => {
                let lhs = lhs.interp_exp(table);
                let rhs = rhs.interp_exp(table);
                match op {
                    BinOp::Plus => lhs + rhs,
                    BinOp::Minus => lhs - rhs,
                    BinOp::Times => lhs * rhs,
                    BinOp::Div => lhs / rhs,
                }
            }
            Exp::Eseq(stm, exp) => {
                stm.interp_exp(table);
                exp.interp_exp(table)
            }
        }
    }
}

impl Stm {
    pub fn maxargs(&self) -> usize {
        match self {
            Stm::Compound(s1, s2) => max(s1.maxargs(), s2.maxargs()),
            Stm::Assign { exp, .. } => exp.maxargs(),
            Stm::Print(vec) => vec.len(),
        }
    }

    pub fn interp_exp(&self, table: &mut BTreeMap<String, isize>) {
        match self {
            Stm::Compound(s1, s2) => {
                s1.interp_exp(table);
                s2.interp_exp(table);
            }
            Stm::Assign { id, exp } => {
                let value = exp.interp_exp(table);
                table.insert(id.clone(), value);
            }
            Stm::Print(vec) => {
                println!(
                    "{}",
                    vec.iter()
                        .map(|exp| exp.interp_exp(table).to_string())
                        .intersperse(" ".into())
                        .collect::<String>()
                );
            }
        }
    }
}
