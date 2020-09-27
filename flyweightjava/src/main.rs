#![feature(box_syntax, box_patterns)]
use std::fmt;
use std::rc::Rc;

type Symbol = Rc<str>;
type Ty = Symbol;

#[derive(Debug, Clone, PartialEq)]
enum Term {
    TmVar(Symbol),
    TmProj(Box<Term>, Symbol),
    TmInvk(Box<Term>, Symbol, Vec<Term>),
    TmNew(Symbol, Vec<Term>),
    TmCast(Box<Term>, Symbol),
}

use Term::*;

struct ClassTable {
    classes: Vec<Class>,
}

struct Class {
    name: Symbol,
    parent: Symbol,
    fields: Vec<(Symbol, Symbol)>,
    methods: Vec<Method>,
}

struct Method {
    name: Symbol,
    ty: Symbol,
    args: Vec<(Symbol, Symbol)>,
    body: Term,
}

// NOTE: dummy implementation
impl ClassTable {
    fn new() -> Self {
        Self { classes: vec![] }
    }

    fn add(&mut self, class: Class) {
        // TODO: validation
        self.classes.push(class);
    }

    fn fields(&self, klass: &Symbol) -> Option<Vec<(Symbol, Symbol)>> {
        if *klass == "Object".into() {
            return Some(vec![]);
        }

        let class = self.classes.iter().find(|class| class.name == *klass)?;
        let mut result = self.fields(&class.parent)?;
        result.extend(class.fields.clone());
        Some(result)
    }

    fn mbody(&self, m: &Symbol, klass: &Symbol) -> Option<(Vec<Symbol>, Term)> {
        let class = self.classes.iter().find(|class| class.name == *klass)?;
        class
            .methods
            .iter()
            .find(|method| method.name == *m)
            .map(|method| {
                (
                    method.args.iter().map(|(_, xi)| xi.clone()).collect(),
                    method.body.clone(),
                )
            })
            .or_else(|| self.mbody(m, &class.parent))
    }

    fn mtype(&self, m: &Symbol, klass: &Symbol) -> Option<(Vec<Ty>, Ty)> {
        let class = self.classes.iter().find(|class| class.name == *klass)?;
        class
            .methods
            .iter()
            .find(|method| method.name == *m)
            .map(|method| {
                (
                    method.args.iter().map(|(mi, _)| mi.clone()).collect(),
                    method.ty.clone(),
                )
            })
            .or_else(|| self.mtype(m, &class.parent))
    }

    fn is_subtype(&self, c: &Symbol, d: &Symbol) -> bool {
        if c == d {
            return true;
        }
        if *c == "Object".into() {
            return false;
        }
        self.classes
            .iter()
            .find(|class| class.name == *c)
            .map(|class| self.is_subtype(&class.parent, d))
            .unwrap_or(false)
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
                let i = ct.fields(c)?.iter().position(|(_, fi)| fi == f)?;
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
                let fs = ct.fields(&klass)?;
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
                let fs = ct.fields(klass)?;
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

// mod parser {
//     use super::*;

//     use nom::{
//         branch::alt,
//         bytes::complete::tag,
//         character::complete::{
//             alpha1, alphanumeric0, char, digit1, multispace0 as ms0, multispace1 as ms1, none_of,
//         },
//         combinator::{map, not, peek, verify},
//         multi::{many0, separated_list, separated_nonempty_list},
//         number::complete::double,
//         sequence::{delimited, pair, preceded, tuple},
//         IResult,
//     };

//     fn parse_term(input: &str) -> IResult<&str, Term> {
//         alt((
//             map(
//                 tuple((parse_term, ms0, char('.'), ms0, identifier)),
//                 |(t, _, _, _, f)| TmProj(box t, f.into()),
//             ),
//             map(preceded(ms0, identifier), |id| TmVar(id.into())),
//         ))(input)
//     }

//     fn identifier(input: &str) -> IResult<&str, String> {
//         map(pair(alpha1, alphanumeric0), |(s1, s2)| {
//             format!("{}{}", s1, s2)
//         })(input)
//     }

//     #[test]
//     fn test_parse_term() {
//         let input = "foo.bar";
//         let result = parse_term(input);
//         assert_eq!(
//             result,
//             Ok(("", TmProj(box TmVar("foo".into()), "bar".into())))
//         );
//     }
// }

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut ct = ClassTable::new();
    ct.add(Class {
        name: "A".into(),
        parent: "Object".into(),
        fields: vec![],
        methods: vec![],
    });
    ct.add(Class {
        name: "B".into(),
        parent: "Object".into(),
        fields: vec![],
        methods: vec![],
    });
    ct.add(Class {
        name: "Pair".into(),
        parent: "Object".into(),
        fields: vec![
            ("Object".into(), "fst".into()),
            ("Object".into(), "snd".into()),
        ],
        methods: vec![Method {
            name: "setfst".into(),
            ty: "Object".into(),
            args: vec![("Object".into(), "newfst".into())],
            body: TmNew(
                "Pair".into(),
                vec![
                    TmVar("newfst".into()),
                    TmProj(TmVar("this".into()).into(), "snd".into()),
                ],
            ),
        }],
    });

    // new Pair(new A(), new B()).setfst(new B()) => new Pair(new B(), new B())
    let t = TmInvk(
        TmNew(
            "Pair".into(),
            vec![TmNew("A".into(), vec![]), TmNew("B".into(), vec![])],
        )
        .into(),
        "setfst".into(),
        vec![TmNew("B".into(), vec![])],
    );
    let u = t.eval(&ct);
    println!("{} => {}: {}", t, u, u.ty(&ct).unwrap());

    // ((Pair) new Pair(new Pair(new A(), new B()), new A()).fst).snd => new B()
    let t = TmProj(
        TmCast(
            box TmProj(
                box TmNew(
                    "Pair".into(),
                    vec![
                        TmNew(
                            "Pair".into(),
                            vec![TmNew("A".into(), vec![]), TmNew("B".into(), vec![])],
                        ),
                        TmNew("A".into(), vec![]),
                    ],
                ),
                "fst".into(),
            ),
            "Pair".into(),
        )
        .into(),
        "snd".into(),
    );
    let u = t.eval(&ct);
    println!("{} => {}: {}", t, u, u.ty(&ct).unwrap());

    Ok(())
}
