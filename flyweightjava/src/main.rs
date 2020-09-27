#![feature(box_syntax, box_patterns)]
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyArr(Box<Ty>, Box<Ty>),
    TyBool,
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(String),
    TmProj(Box<Term>, String),
    TmInvk(Box<Term>, String, Vec<Term>),
    TmNew(String, Vec<Term>),
    TmCast(Box<Term>, String),
}

pub struct ClassTable {}

// NOTE: dummy implementation
impl ClassTable {
    fn new() -> Self {
        Self {}
    }

    fn fields(&self, klass: &str) -> Vec<(String, String)> {
        if klass == "Pair" {
            return vec![
                ("Object".into(), "fst".into()),
                ("Object".into(), "snd".into()),
            ];
        }
        vec![]
    }

    fn mbody(&self, m: &str, klass: &str) -> Option<(Vec<String>, Term)> {
        if klass == "Pair" && m == "setfst" {
            return Some((
                vec!["newfst".into()],
                TmNew(
                    "Pair".into(),
                    vec![
                        TmVar("newfst".into()),
                        TmProj(TmVar("this".into()).into(), "snd".into()),
                    ],
                ),
            ));
        }

        None
    }
}

impl Term {
    fn is_val(&self) -> bool {
        match self {
            TmNew(_, _) => true,
            _ => false,
        }
    }

    fn subst(&self, u: &str, t: &Self) -> Self {
        match self {
            TmVar(v) if u == v => t.clone(),
            TmVar(_) => self.clone(),
            TmProj(s, f) => TmProj(box s.subst(u, t), f.clone()),
            TmInvk(s, m, xs) => TmInvk(
                box s.subst(u, t),
                m.clone(),
                xs.iter().map(|x| x.subst(u, t)).collect(),
            ),
            TmNew(c, xs) => TmNew(c.clone(), xs.iter().map(|x| x.subst(u, t)).collect()),
            TmCast(s, c) => TmCast(box s.subst(u, t), c.clone()),
        }
    }

    fn eval1(&self, ct: &ClassTable) -> Option<Self> {
        match self {
            // E-ProjNew
            TmProj(box TmNew(c, vs), f) => {
                let i = ct.fields(c).iter().position(|(_, fi)| fi == f)?;
                Some(vs[i].clone())
            }
            // E-InvkNew
            TmInvk(box TmNew(c, vs), m, us) => {
                let (xs, t) = ct.mbody(m, c)?;
                let mut result = t.subst("this", &TmNew(c.clone(), vs.clone()));
                for (xi, ui) in xs.iter().zip(us.iter()) {
                    result = result.subst(xi, ui);
                }
                Some(result)
            }
            // E-CastNew (TODO)
            // E-Field
            TmProj(t, f) if !t.is_val() => Some(TmProj(box t.eval1(ct)?, f.clone())),
            // E-InvkRecv
            TmInvk(t, m, vs) if !t.is_val() => {
                Some(TmInvk(box t.eval1(ct)?, m.clone(), vs.clone()))
            }
            // E-InvkArg
            TmInvk(t, m, vs) if vs.iter().any(|v| !v.is_val()) => {
                let (i, ui) = vs
                    .iter()
                    .enumerate()
                    .find_map(|(i, vi)| Some(i).zip(vi.eval1(ct)))?;
                let mut us = vs.clone();
                us[i] = ui;
                Some(TmInvk(t.clone(), m.clone(), us))
            }
            // E-NewArg
            TmNew(c, vs) if vs.iter().any(|v| !v.is_val()) => {
                let (i, ui) = vs
                    .iter()
                    .enumerate()
                    .find_map(|(i, vi)| Some(i).zip(vi.eval1(ct)))?;
                let mut us = vs.clone();
                us[i] = ui;
                Some(TmNew(c.clone(), us))
            }
            // E-Cast
            TmCast(t, c) if !t.is_val() => Some(TmCast(box t.eval1(ct)?, c.clone())),
            _ => None,
        }
    }

    fn eval(&self, ct: &ClassTable) -> Self {
        let mut t = self.clone();
        while let Some(n) = t.eval1(ct) {
            t = n;
        }
        t
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmVar(x) => write!(f, "{}", x),
            TmProj(t, p) => write!(f, "{}.{}", t, p),
            TmInvk(t, m, vs) => write!(
                f,
                "{}.{}({})",
                t,
                m,
                vs.iter()
                    .map(|vi| format!("{}", vi))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TmNew(c, vs) => write!(
                f,
                "new {}({})",
                c,
                vs.iter()
                    .map(|vi| format!("{}", vi))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TmCast(t, c) => write!(f, "(({}) {})", c, t),
        }
    }
}

use Term::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // new Pair(new A(), new B()).setfst(new B())
    let t = TmInvk(
        TmNew(
            "Pair".into(),
            vec![TmNew("A".into(), vec![]), TmNew("B".into(), vec![])],
        )
        .into(),
        "setfst".into(),
        vec![TmNew("B".into(), vec![])],
    );
    println!("{}", t.eval(&ClassTable::new()));
    Ok(())
}
