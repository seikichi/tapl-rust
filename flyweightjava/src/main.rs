#![feature(box_syntax, box_patterns)]
use std::fmt;
use std::rc::Rc;

type Symbol = Rc<str>;
type Ty = Symbol;

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(Symbol),
    TmProj(Box<Term>, Symbol),
    TmInvk(Box<Term>, Symbol, Vec<Term>),
    TmNew(Symbol, Vec<Term>),
    TmCast(Box<Term>, Symbol),
}

use Term::*;

pub struct ClassTable {}

// NOTE: dummy implementation
impl ClassTable {
    fn new() -> Self {
        Self {}
    }

    fn fields(&self, klass: &Symbol) -> Vec<(Symbol, Symbol)> {
        if *klass == "Pair".into() {
            return vec![
                ("Object".into(), "fst".into()),
                ("Object".into(), "snd".into()),
            ];
        }
        vec![]
    }

    fn mbody(&self, m: &Symbol, klass: &Symbol) -> Option<(Vec<Symbol>, Term)> {
        if *klass == "Pair".into() && *m == "setfst".into() {
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

    fn mtype(&self, m: &Symbol, klass: &Symbol) -> Option<(Vec<Ty>, Ty)> {
        if *klass == "Pair".into() && *m == "setfst".into() {
            return Some((vec!["Object".into()], "Pair".into()));
        }
        None
    }

    fn is_subtype(&self, c: &Symbol, d: &Symbol) -> bool {
        *c == *d || *d == "Object".into()
    }
}

impl Term {
    fn is_val(&self) -> bool {
        match self {
            TmNew(_, _) => true,
            _ => false,
        }
    }

    fn subst(&self, u: &Symbol, t: &Self) -> Self {
        match self {
            TmVar(v) if u == v => t.clone(),
            TmVar(_) => self.clone(),
            TmProj(s, f) => TmProj(box s.subst(u, t), f.clone()),
            TmInvk(s, m, ts) => TmInvk(
                box s.subst(u, t),
                m.clone(),
                ts.iter().map(|ti| ti.subst(u, t)).collect(),
            ),
            TmNew(c, ts) => TmNew(c.clone(), ts.iter().map(|ti| ti.subst(u, t)).collect()),
            TmCast(s, c) => TmCast(box s.subst(u, t), c.clone()),
        }
    }

    fn eval1(&self, ct: &ClassTable) -> Option<Self> {
        match self {
            // E-ProjNew
            TmProj(box TmNew(c, ts), f) => {
                let i = ct.fields(c).iter().position(|(_, fi)| fi == f)?;
                Some(ts[i].clone())
            }
            // E-InvkNew
            TmInvk(box TmNew(c, ts), m, us) => {
                let (xs, t) = ct.mbody(m, c)?;
                let mut result = t.subst(&"this".into(), &TmNew(c.clone(), ts.clone()));
                for (xi, ui) in xs.iter().zip(us.iter()) {
                    result = result.subst(xi, ui);
                }
                Some(result)
            }
            // E-CastNew
            TmCast(box TmNew(c, ts), d) if ct.is_subtype(c, d) => {
                Some(TmNew(c.clone(), ts.clone()))
            }
            // E-Field
            TmProj(t, f) if !t.is_val() => Some(TmProj(box t.eval1(ct)?, f.clone())),
            // E-InvkRecv
            TmInvk(t, m, ts) if !t.is_val() => {
                Some(TmInvk(box t.eval1(ct)?, m.clone(), ts.clone()))
            }
            // E-InvkArg
            TmInvk(t, m, ts) if ts.iter().any(|ti| !ti.is_val()) => {
                let (i, ti) = ts
                    .iter()
                    .enumerate()
                    .find_map(|(i, ti)| Some(i).zip(ti.eval1(ct)))?;
                let mut ts = ts.clone();
                ts[i] = ti;
                Some(TmInvk(t.clone(), m.clone(), ts))
            }
            // E-NewArg
            TmNew(c, ts) if ts.iter().any(|ti| !ti.is_val()) => {
                let (i, ti) = ts
                    .iter()
                    .enumerate()
                    .find_map(|(i, ti)| Some(i).zip(ti.eval1(ct)))?;
                let mut ts = ts.clone();
                ts[i] = ti;
                Some(TmNew(c.clone(), ts))
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

    fn ty(&self, ct: &ClassTable) -> Option<Ty> {
        match self {
            // T-Field
            TmProj(t, f) => {
                let klass = t.ty(ct)?;
                let fs = ct.fields(&klass);
                fs.iter().find(|(_, fi)| fi == f).map(|(c, _)| c.clone())
            }
            // T-Invk
            TmInvk(t, m, ts) => {
                let klass = t.ty(ct)?;
                let (ds, c) = ct.mtype(m, &klass)?;

                if ds.len() != ts.len() {
                    return None;
                }
                for (d, t) in ds.iter().zip(ts.iter()) {
                    let c = t.ty(ct)?;
                    if !ct.is_subtype(&c, d) {
                        return None;
                    }
                }
                Some(c)
            }
            // T-New
            TmNew(klass, ts) => {
                let fs = ct.fields(klass);
                if fs.len() != ts.len() {
                    return None;
                }
                for ((d, _), t) in fs.iter().zip(ts.iter()) {
                    let c = t.ty(ct)?;
                    if !ct.is_subtype(&c, d) {
                        return None;
                    }
                }
                Some(klass.clone())
            }
            // T-Ucast
            // T-Dcast
            // T-Scast
            TmCast(_, c) => Some(c.clone()),
            _ => None,
        }
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
    let ct = ClassTable::new();
    let t = t.eval(&ct);
    println!("{}: {}", t, t.ty(&ct).unwrap());

    Ok(())
}
