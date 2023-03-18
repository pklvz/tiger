#![feature(iter_intersperse)]

mod straightline;

use std::collections::BTreeMap;
use straightline::{BinOp, Exp, Stm};

fn main() {
    let prog = Stm::Compound(
        Stm::Assign {
            id: "a".into(),
            exp: Exp::Op(Exp::Num(5).into(), BinOp::Plus, Exp::Num(3).into()),
        }
        .into(),
        Stm::Compound(
            Stm::Assign {
                id: "b".into(),
                exp: Exp::Eseq(
                    Stm::Print(vec![
                        Exp::Id("a".into()),
                        Exp::Op(Exp::Id("a".into()).into(), BinOp::Minus, Exp::Num(1).into()),
                    ])
                    .into(),
                    Exp::Op(
                        Exp::Num(10).into(),
                        BinOp::Times,
                        Exp::Id("a".into()).into(),
                    )
                    .into(),
                ),
            }
            .into(),
            Stm::Print(vec![Exp::Id("b".into())]).into(),
        )
        .into(),
    );
    println!("{}", prog.maxargs());
    let mut table = BTreeMap::new();
    prog.interp_exp(&mut table);
}
