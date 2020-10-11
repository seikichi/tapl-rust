#![feature(box_syntax, box_patterns)]

use std::env;
use std::fmt;
use std::fs;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyVar(usize),
    TyArr(Box<Ty>, Box<Ty>),
    TyAll(Rc<str>, Box<Ty>),
    TySome(Rc<str>, Box<Ty>),
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(usize),
    TmAbs(Rc<str>, Ty, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmTAbs(Rc<str>, Box<Term>),
    TmTApp(Box<Term>, Ty),
    TmPack(Ty, Box<Term>, Ty),
    TmUnpack(Rc<str>, Rc<str>, Box<Term>, Box<Term>),
}

#[derive(Clone, Debug)]
pub enum Binding {
    NameBind,
    VarBind(Ty),
    TyVarBind,
    TyAbbBind(Ty),
    TmAbbBind(Term, Option<Ty>),
}

#[derive(Debug)]
pub enum Command {
    Eval(Term),
    Bind(Rc<str>, Binding),
    SomeBind(Rc<str>, Rc<str>, Term),
}

use Binding::*;
use Command::*;
use Term::*;
use Ty::*;

#[derive(Clone, Debug)]
pub struct Context {
    bindings: Vec<(String, Binding)>,
}

impl Context {
    fn new() -> Self {
        Self { bindings: vec![] }
    }

    fn add_binding(&mut self, x: String, bind: Binding) {
        self.bindings.push((x, bind));
    }

    fn add_name(&mut self, x: String) {
        self.add_binding(x, NameBind);
    }

    fn with_binding<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, bind: Binding, f: F) -> R {
        self.add_binding(x, bind);
        let result = f(self);
        self.bindings.pop();
        result
    }

    fn with_name<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, f: F) -> R {
        self.with_binding(x, NameBind, f)
    }

    fn index2name(&self, x: usize) -> Option<&String> {
        if self.bindings.len() <= x {
            return None;
        }
        self.bindings
            .get(self.bindings.len() - x - 1)
            .map(|(s, _)| s)
    }

    fn name2index(&self, x: &str) -> Option<usize> {
        self.bindings.iter().rev().position(|(y, _)| y == x)
    }

    fn get_binding(&self, i: usize) -> Binding {
        let bind = &self.bindings[self.bindings.len() - i - 1].1;
        bind.shift(i as i32 + 1)
    }

    fn get_type(&self, i: usize) -> Ty {
        match self.get_binding(i) {
            VarBind(ty) => ty,
            TmAbbBind(_, Some(ty)) => ty,
            _ => panic!("Wrong kind of binding for variable"),
        }
    }

    fn with_fresh_name<R, F: FnOnce(&mut Self, String) -> R>(&mut self, x: &str, f: F) -> R {
        let mut name: String = x.into();
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        self.with_name(name.clone(), move |ctx| f(ctx, name))
    }

    fn is_name_bound(&self, x: &str) -> bool {
        self.bindings.iter().any(|(s, _)| s == x)
    }
}

impl Term {
    fn map<F: Copy + Fn(i32, usize) -> Self, TF: Copy + Fn(i32, &Ty) -> Ty>(
        &self,
        c: i32,
        onvar: F,
        ontype: TF,
    ) -> Self {
        match &self {
            TmVar(x) => onvar(c, *x),
            TmAbs(x, ty1, t2) => TmAbs(x.clone(), ontype(c, ty1), box t2.map(c + 1, onvar, ontype)),
            TmApp(t1, t2) => TmApp(box t1.map(c, onvar, ontype), box t2.map(c, onvar, ontype)),
            TmTAbs(tyx, t2) => TmTAbs(tyx.clone(), box t2.map(c + 1, onvar, ontype)),
            TmTApp(t1, ty2) => TmTApp(box t1.map(c, onvar, ontype), ontype(c, ty2)),
            TmPack(ty1, t2, ty3) => {
                TmPack(ontype(c, ty1), box t2.map(c, onvar, ontype), ontype(c, ty3))
            }
            TmUnpack(tyx, x, t1, t2) => TmUnpack(
                tyx.clone(),
                x.clone(),
                box t1.map(c, onvar, ontype),
                box t2.map(c + 2, onvar, ontype),
            ),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(
            c,
            |c, x| {
                if x as i32 >= c {
                    TmVar((x as i32 + d) as usize)
                } else {
                    TmVar(x)
                }
            },
            |c, ty| ty.shift_above(d, c),
        )
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(
            j,
            |j, x| if x as i32 == j { s.shift(j) } else { TmVar(x) },
            |_, ty| ty.clone(),
        )
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn ty_subst(&self, j: i32, ty: &Ty) -> Self {
        self.map(j, |_, x| TmVar(x), |j, ty2| ty.subst(j, ty2))
    }

    fn ty_subst_top(&self, ty: &Ty) -> Self {
        self.ty_subst(0, &ty.shift(1)).shift(-1)
    }

    fn is_val(&self, ctx: &Context) -> bool {
        match &self {
            TmAbs(_, _, _) => true,
            TmPack(_, v1, _) if v1.is_val(ctx) => true,
            TmTAbs(_, _) => true,
            _ => false,
        }
    }

    fn eval1(&self, ctx: &Context) -> Option<Self> {
        Some(match self {
            // TmApp
            TmApp(box TmAbs(_, _, t12), v2) if v2.is_val(ctx) => t12.subst_top(v2),
            TmApp(v1, t2) if v1.is_val(ctx) => TmApp(v1.clone(), box t2.eval1(ctx)?),
            TmApp(t1, t2) => TmApp(box t1.eval1(ctx)?, t2.clone()),
            // TmUnpack, TmPack
            TmUnpack(_, _, box TmPack(ty11, v12, _), t2) if v12.is_val(ctx) => {
                v12.shift(1).subst_top(t2).ty_subst_top(ty11)
            }
            TmUnpack(tyx, x, t1, t2) => {
                TmUnpack(tyx.clone(), x.clone(), box t1.eval1(ctx)?, t2.clone())
            }
            TmPack(ty1, t2, ty3) => TmPack(ty1.clone(), box t2.eval1(ctx)?, ty3.clone()),
            // Var
            TmVar(n) => match ctx.get_binding(*n) {
                TmAbbBind(t, _) => t.clone(),
                _ => return None,
            },
            // TmTApp
            TmTApp(box TmTAbs(x, t11), ty2) => t11.ty_subst_top(ty2),
            TmTApp(t1, ty2) => TmTApp(box t1.eval1(ctx)?, ty2.clone()),
            // Other
            _ => return None,
        })
    }

    fn eval(&self, ctx: &Context) -> Self {
        let mut t = self.clone();
        while let Some(n) = t.eval1(ctx) {
            t = n;
        }
        t
    }
}

impl Ty {
    fn map<F: Copy + Fn(i32, usize) -> Self>(&self, c: i32, onvar: F) -> Self {
        match &self {
            TyVar(x) => onvar(c, *x),
            TyArr(ty1, ty2) => TyArr(box ty1.map(c, onvar), box ty2.map(c, onvar)),
            TyAll(tyx, ty2) => TyAll(tyx.clone(), box ty2.map(c + 1, onvar)),
            TySome(tyx, ty2) => TySome(tyx.clone(), box ty2.map(c + 1, onvar)),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(c, |c, x| {
            if x as i32 >= c {
                TyVar((x as i32 + d) as usize)
            } else {
                TyVar(x)
            }
        })
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(j, |j, x| if x as i32 == j { s.shift(j) } else { TyVar(x) })
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }
}

impl Binding {
    fn shift(&self, d: i32) -> Self {
        match self {
            NameBind => NameBind,
            TyVarBind => TyVarBind,
            TyAbbBind(ty) => TyAbbBind(ty.shift(d)),
            VarBind(ty) => VarBind(ty.shift(d)),
            TmAbbBind(t, None) => TmAbbBind(t.shift(d), None),
            TmAbbBind(t, Some(ty)) => TmAbbBind(t.shift(d), Some(ty.shift(d))),
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

//     type ParseResult<T> = Box<dyn Fn(&mut Context) -> T>;

//     pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
//         map(separated_list(pair(ms0, char(';')), command), |fs| {
//             let mut ctx = Context::new();
//             fs.iter().map(|f| f(&mut ctx)).collect()
//         })(input)
//     }

//     fn command(input: &str) -> IResult<&str, ParseResult<Command>> {
//         alt((
//             map(
//                 pair(preceded(ms0, identifier), binder),
//                 |(id, f)| -> ParseResult<_> {
//                     box move |ctx| {
//                         let result = Bind(id.clone(), f(ctx));
//                         ctx.add_name(id.clone());
//                         result
//                     }
//                 },
//             ),
//             map(term, |f| -> ParseResult<_> { box move |ctx| Eval(f(ctx)) }),
//         ))(input)
//     }

//     fn binder(input: &str) -> IResult<&str, ParseResult<Binding>> {
//         alt((
//             map(
//                 preceded(tuple((ms0, char(':'), ms0)), all_type),
//                 |f| -> ParseResult<_> { box move |ctx| VarBind(f(ctx)) },
//             ),
//             map(
//                 preceded(tuple((ms0, char('='), ms0)), term),
//                 |f| -> ParseResult<_> { box move |ctx| TmAbbBind(f(ctx), None) },
//             ),
//         ))(input)
//     }

//     fn all_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
//         preceded(ms0, arrow_type)(input)
//     }

//     fn atomic_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
//         alt((
//             map(preceded(ms0, tag("Bool")), |_| -> ParseResult<_> {
//                 box |_ctx| TyBool
//             }),
//             map(preceded(ms0, tag("Unit")), |_| -> ParseResult<_> {
//                 box |_ctx| TyUnit
//             }),
//             map(preceded(ms0, tag("String")), |_| -> ParseResult<_> {
//                 box |_ctx| TyString
//             }),
//             map(preceded(ms0, tag("Float")), |_| -> ParseResult<_> {
//                 box |_ctx| TyFloat
//             }),
//             map(preceded(ms0, tag("Nat")), |_| -> ParseResult<_> {
//                 box |_ctx| TyNat
//             }),
//             map(
//                 preceded(
//                     ms0,
//                     delimited(char('{'), field_types, preceded(ms0, char('}'))),
//                 ),
//                 |f| -> ParseResult<_> { box move |ctx| TyRecord(f(ctx)) },
//             ),
//             map(
//                 preceded(
//                     ms0,
//                     delimited(char('<'), field_types, preceded(ms0, char('>'))),
//                 ),
//                 |f| -> ParseResult<_> { box move |ctx| TyVariant(f(ctx)) },
//             ),
//             preceded(
//                 ms0,
//                 delimited(char('('), all_type, preceded(ms0, char(')'))),
//             ),
//         ))(input)
//     }

//     fn field_types(input: &str) -> IResult<&str, ParseResult<Vec<(String, Ty)>>> {
//         map(
//             separated_list(pair(ms0, char(',')), field_type),
//             |fs| -> ParseResult<_> {
//                 box move |ctx| fs.iter().enumerate().map(|(i, f)| f(ctx, i + 1)).collect()
//             },
//         )(input)
//     }

//     type FieldTypeResult = Box<dyn Fn(&mut Context, usize) -> (String, Ty)>;

//     fn field_type(input: &str) -> IResult<&str, FieldTypeResult> {
//         alt((
//             map(
//                 tuple((label, ms0, char(':'), all_type)),
//                 |(l, _, _, f)| -> FieldTypeResult { box move |ctx, _| (l.clone(), f(ctx)) },
//             ),
//             map(all_type, |f| -> FieldTypeResult {
//                 box move |ctx, i| (format!("{}", i), f(ctx))
//             }),
//         ))(input)
//     }
//     fn arrow_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
//         map(
//             separated_nonempty_list(pair(ms0, tag("->")), atomic_type),
//             |fs| {
//                 let mut it = fs.into_iter().rev();
//                 let f = it.next().unwrap();
//                 it.fold(f, |f1, f2| box move |ctx| TyArr(box f2(ctx), box f1(ctx)))
//             },
//         )(input)
//     }

//     pub fn term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         alt((
//             if_term,
//             lambda,
//             let_term,
//             letrec_term,
//             assign,
//             case,
//             app_term,
//         ))(input)
//     }

//     fn case(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("case")),
//                 term,
//                 preceded(ms0, tag("of")),
//                 cases,
//             )),
//             |(_, tf, _, cf)| -> ParseResult<_> { box move |ctx| TmCase(box tf(ctx), cf(ctx)) },
//         )(input)
//     }

//     fn cases(input: &str) -> IResult<&str, ParseResult<Vec<(String, (String, Term))>>> {
//         map(
//             separated_nonempty_list(pair(ms0, char('|')), single_case),
//             |fs| -> ParseResult<_> { box move |ctx| fs.iter().map(|f| f(ctx)).collect() },
//         )(input)
//     }

//     fn single_case(input: &str) -> IResult<&str, ParseResult<(String, (String, Term))>> {
//         map(
//             tuple((
//                 preceded(ms0, char('<')),
//                 label,
//                 preceded(ms0, char('=')),
//                 label,
//                 preceded(ms0, char('>')),
//                 preceded(ms0, tag("=>")),
//                 app_term,
//             )),
//             |(_, l1, _, l2, _, _, ft)| -> ParseResult<_> {
//                 box move |ctx| {
//                     (
//                         l1.clone(),
//                         (l2.clone(), ctx.with_name(l2.clone(), |ctx| ft(ctx))),
//                     )
//                 }
//             },
//         )(input)
//     }

//     fn lambda(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, alt((tag("lambda"), tag("λ")))),
//                 preceded(ms1, identifier),
//                 preceded(ms0, char(':')),
//                 all_type,
//                 preceded(ms0, char('.')),
//                 term,
//             )),
//             |(_, s, _, tyf, _, tf)| -> ParseResult<_> {
//                 box move |ctx| {
//                     ctx.with_name(s.clone(), |mut ctx| {
//                         TmAbs(s.clone(), tyf(&mut ctx), box tf(&mut ctx))
//                     })
//                 }
//             },
//         )(input)
//     }

//     fn assign(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((app_term, preceded(ms0, tag(":=")), app_term)),
//             |(f1, _, f2)| -> ParseResult<_> { box move |ctx| TmAssign(box f1(ctx), box f2(ctx)) },
//         )(input)
//     }

//     fn let_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("let")),
//                 preceded(ms1, identifier),
//                 preceded(ms0, char('=')),
//                 term,
//                 preceded(ms1, tag("in")),
//                 preceded(ms1, term),
//             )),
//             |(_, s, _, f1, _, f2)| -> ParseResult<_> {
//                 box move |ctx| {
//                     let t1 = f1(ctx);
//                     ctx.with_name(s.clone(), |ctx| TmLet(s.clone(), box t1, box f2(ctx)))
//                 }
//             },
//         )(input)
//     }

//     fn letrec_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("letrec")),
//                 preceded(ms1, identifier),
//                 preceded(ms0, char(':')),
//                 preceded(ms0, all_type),
//                 preceded(ms0, char('=')),
//                 term,
//                 preceded(ms1, tag("in")),
//                 preceded(ms1, term),
//             )),
//             |(_, s, _, fty, _, f1, _, f2)| -> ParseResult<_> {
//                 box move |ctx| {
//                     let ty = fty(ctx);
//                     ctx.with_name(s.clone(), |ctx| {
//                         TmLet(
//                             s.clone(),
//                             box TmFix(box TmAbs(s.clone(), ty, box f1(ctx))),
//                             box f2(ctx),
//                         )
//                     })
//                 }
//             },
//         )(input)
//     }

//     fn if_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("if")),
//                 term,
//                 preceded(ms1, tag("then")),
//                 term,
//                 preceded(ms1, tag("else")),
//                 term,
//             )),
//             |(_, f1, _, f2, _, f3)| -> ParseResult<_> {
//                 box move |ctx| TmIf(box f1(ctx), box f2(ctx), box f3(ctx))
//             },
//         )(input)
//     }

//     fn app_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(separated_nonempty_list(ms1, app_term_1), |fs| {
//             let mut it = fs.into_iter();
//             let f = it.next().unwrap();
//             it.fold(f, |f1, f2| box move |ctx| TmApp(box f1(ctx), box f2(ctx)))
//         })(input)
//     }

//     fn app_term_1(input: &str) -> IResult<&str, ParseResult<Term>> {
//         alt((
//             map(
//                 preceded(pair(ms0, tag("fix")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmFix(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("succ")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmSucc(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("pred")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmPred(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("iszero")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmIsZero(box f(ctx)) },
//             ),
//             map(
//                 tuple((pair(ms0, tag("timesfloat")), path_term, path_term)),
//                 |(_, f1, f2)| -> ParseResult<_> {
//                     box move |ctx| TmTimesFloat(box f1(ctx), box f2(ctx))
//                 },
//             ),
//             map(
//                 preceded(pair(ms0, tag("ref")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmRef(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("!")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmDeref(box f(ctx)) },
//             ),
//             path_term,
//         ))(input)
//     }

//     fn path_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             pair(ascribe_term, many0(preceded(pair(ms0, char('.')), label))),
//             |(tf, ls)| -> ParseResult<_> {
//                 box move |ctx| ls.iter().fold(tf(ctx), |t, li| TmProj(box t, li.clone()))
//             },
//         )(input)
//     }

//     fn label(input: &str) -> IResult<&str, String> {
//         preceded(
//             ms0,
//             alt((identifier, map(digit1, |s: &str| s.parse().unwrap()))),
//         )(input)
//     }

//     fn ascribe_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         alt((
//             map(
//                 tuple((atomic_term, ms1, tag("as"), ms1, all_type)),
//                 |(ft, _, _, _, fty)| -> ParseResult<_> {
//                     box move |ctx| TmAscribe(box ft(ctx), fty(ctx))
//                 },
//             ),
//             atomic_term,
//         ))(input)
//     }

//     fn term_seq(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(separated_nonempty_list(pair(ms0, char(';')), term), |fs| {
//             let mut it = fs.into_iter().rev();
//             let f = it.next().unwrap();
//             it.fold(f, |f1, f2| {
//                 box move |ctx| {
//                     TmApp(
//                         box TmAbs(
//                             "_".into(),
//                             TyUnit,
//                             ctx.with_name("_".into(), |ctx| box f1(ctx)),
//                         ),
//                         box f2(ctx),
//                     )
//                 }
//             })
//         })(input)
//     }

//     fn atomic_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         preceded(
//             ms0,
//             alt((
//                 map(tag("true"), |_| -> ParseResult<_> { box |_| TmTrue }),
//                 map(tag("false"), |_| -> ParseResult<_> { box |_| TmFalse }),
//                 map(tag("unit"), |_| -> ParseResult<_> { box |_| TmUnit }),
//                 map(identifier, |s| -> ParseResult<_> {
//                     box move |ctx| TmVar(ctx.name2index(&s).expect(&format!("{} not found", s)))
//                 }),
//                 delimited(char('('), term_seq, pair(ms0, char(')'))),
//                 // String
//                 map(string_value, |s: String| -> ParseResult<_> {
//                     box move |_| TmString(s.clone())
//                 }),
//                 // Nat
//                 map(int_value, |n| -> ParseResult<_> {
//                     box move |_| {
//                         let mut result = TmZero;
//                         for _ in 0..n {
//                             result = TmSucc(box result);
//                         }
//                         result
//                     }
//                 }),
//                 map(double, |d| -> ParseResult<_> { box move |_| TmFloat(d) }),
//                 // Record
//                 map(
//                     delimited(char('{'), fields, pair(ms0, char('}'))),
//                     |fs| -> ParseResult<_> { box move |ctx| TmRecord(fs(ctx)) },
//                 ),
//                 // Tag
//                 map(
//                     tuple((
//                         char('<'),
//                         label,
//                         preceded(ms0, char('=')),
//                         term,
//                         preceded(ms0, char('>')),
//                         preceded(ms0, tag("as")),
//                         all_type,
//                     )),
//                     |(_, l, _, ft, _, _, fty)| -> ParseResult<_> {
//                         box move |ctx| TmTag(l.clone(), box ft(ctx), fty(ctx))
//                     },
//                 ),
//             )),
//         )(input)
//     }

//     fn fields(input: &str) -> IResult<&str, ParseResult<Vec<(String, Term)>>> {
//         map(
//             separated_list(pair(ms0, char(',')), field),
//             |fs| -> ParseResult<_> {
//                 box move |ctx| fs.iter().enumerate().map(|(i, f)| f(ctx, i + 1)).collect()
//             },
//         )(input)
//     }

//     type FieldResult = Box<dyn Fn(&mut Context, usize) -> (String, Term)>;

//     fn field(input: &str) -> IResult<&str, FieldResult> {
//         alt((
//             map(
//                 tuple((label, ms0, char('='), term)),
//                 |(l, _, _, f)| -> FieldResult { box move |ctx, _| (l.clone(), f(ctx)) },
//             ),
//             map(term, |f| -> FieldResult {
//                 box move |ctx, i| (format!("{}", i), f(ctx))
//             }),
//         ))(input)
//     }

//     const RESERVED_KEYWORDS: &'static [&'static str] = &[
//         "true", "false", "if", "then", "else", "succ", "pred", "iszero", "let", "in", "fix",
//         "unit", "ref", "case", "of",
//     ];

//     fn identifier(input: &str) -> IResult<&str, String> {
//         verify(
//             map(pair(alpha1, alphanumeric0), |(s1, s2)| {
//                 format!("{}{}", s1, s2)
//             }),
//             |s: &String| !RESERVED_KEYWORDS.iter().any(|x| x == &s),
//         )(input)
//     }

//     fn int_value(input: &str) -> IResult<&str, u32> {
//         map(pair(digit1, not(peek(char('.')))), |(s, _): (&str, _)| {
//             s.parse().unwrap()
//         })(input)
//     }

//     fn string_value(input: &str) -> IResult<&str, String> {
//         map(delimited(char('"'), many0(none_of("\"")), char('"')), |s| {
//             s.iter().collect()
//         })(input)
//     }
// }

// #[test]
// fn test() {
//     let testcases = vec![
//         // Bool,
//         ("true", "true", "Bool"),
//         (
//             "(λ x: Bool -> Bool. if x true then true else false) (λ x: Bool. x)",
//             "true",
//             "Bool",
//         ),
//         (
//             "(λ x: Bool -> Bool -> Bool. x true false) (λ x: Bool. λ y: Bool. true)",
//             "true",
//             "Bool",
//         ),
//         // Unit
//         ("unit", "unit", "Unit"),
//         ("λ x: Bool. unit", "λ x: Bool. unit", "Bool -> Unit"),
//         ("(λ x: Bool. unit) true", "unit", "Unit"),
//         // Seq
//         ("(unit; 42)", "42", "Nat"),
//         (
//             "λ x: Bool. (unit; 42)",
//             "λ x: Bool. (λ _: Unit. 42) unit",
//             "Bool -> Nat",
//         ),
//         // Nat
//         ("(λ x: Nat. succ x) 41", "42", "Nat"),
//         ("(λ x: Nat. if iszero x then 42 else 0) 0", "42", "Nat"),
//         ("(λ x: Nat. if iszero x then 42 else 0) 1", "0", "Nat"),
//         // String
//         (r#""hello""#, r#""hello""#, "String"),
//         (r#"λ x: Bool. "hello""#, r#"λ x: Bool. "hello""#, "Bool -> String"),
//         // Float
//         ("1.2", "1.2", "Float"),
//         ("timesfloat 2.5 2.0", "5", "Float"),
//         ("λ x: Float. timesfloat x 2.0", "λ x: Float. timesfloat x 2", "Float -> Float"),
//         // Let
//         ("let x=true in x", "true", "Bool"),
//         ("let x=0 in let f=λ x: Nat. succ x in f x", "1", "Nat"),
//         // Fix
//         (
//             "(fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then n else succ (f (pred m) n))) 40 2",
//             "42",
//             "Nat",
//         ),
//         // Letrec
//         (
//             "
//             letrec plus: Nat -> Nat -> Nat =
//               λ m: Nat. λ n: Nat.
//                 if iszero m then n else succ (plus (pred m) n) in
//             letrec times: Nat -> Nat -> Nat =
//               λ m: Nat. λ n: Nat.
//                 if iszero m then 0 else plus n (times (pred m) n) in
//             letrec factorial: Nat -> Nat =
//               λ m: Nat.
//                 if iszero m then 1 else times m (factorial (pred m)) in
//             factorial 5
//             ",
//             "120",
//             "Nat",
//         ),
//         // As
//         ("true as Bool", "true", "Bool"),
//         ("λ x:Bool. x as Bool", "λ x: Bool. x as Bool", "Bool -> Bool"),
//         // Ref
//         ("let r = ref 40 in (r := succ(!r); r := succ(!r); !r)", "42", "Nat"),
//         // TmAbbBind
//         ("x = 41; succ x", "42", "Nat"),
//         ("r = ref 40; r := succ(!r); r := succ(!r); !r", "42", "Nat"),
//         (
//             "
//             z = 0;
//             plus = fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then n else succ (f (pred m) n));
//             times = fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then z else plus n (f (pred m) n));
//             times 6 7
//             ",
//             "42",
//             "Nat"
//         ),
//         // Record
//         ("{x=true, y=1}", "{x = true, y = 1}", "{x: Bool, y: Nat}"),
//         ("{x=true, y=1}.x", "true", "Bool"),
//         ("{true, 1}", "{1 = true, 2 = 1}", "{1: Bool, 2: Nat}"),
//         ("{true, 1}.1", "true", "Bool"),
//         ("{1, {2, {3}}}.2.2.1", "3", "Nat"),
//         ("{x = (λ x: Nat. succ x) 0, y = succ 10}", "{x = 1, y = 11}", "{x: Nat, y: Nat}"),
//         ("(λ r: {x: Nat, y: Bool}. r.x) {x = 42, y = true}", "42", "Nat"),
//         // Variant
//         ("λ x: <a: Bool, b: Bool>. x", "λ x: <a: Bool, b: Bool>. x", "<a: Bool, b: Bool> -> <a: Bool, b: Bool>"),
//         ("<x = 10> as <x: Nat, b: Bool>", "<x = 10> as <x: Nat, b: Bool>", "<x: Nat, b: Bool>"),
//         (
//             "(λ o: <some: Nat, none: Unit>. case o of <some = n> => succ (n) | <none = u> => 0) <none = unit> as <some: Nat, none: Unit>",
//             "0",
//             "Nat",
//         ),
//         (
//             "
//             s = λ o: <some: Nat, none: Unit>.
//                   case o of <some = n> => succ (n)
//                           | <none = u> => 0;
//             o = <some = 10> as <some: Nat, none: Unit>;
//             s o;
//             ",
//             "11",
//             "Nat"
//         ),
//         // Other
//         (
//             "
//             counter = λ c: Nat. let v = ref c in {inc=λ u: Unit. (v := succ (!v); !v), dec=λ u: Unit. (v := pred (!v); !v)};
//             c = counter 10;
//             c.inc unit;
//             c.inc unit;
//             c.dec unit;
//             c.inc unit;
//             ",
//             "12",
//             "Nat",
//         ),
//     ];

//     for (input, expect_term, expect_ty) in testcases {
//         let result = parser::parse(input);
//         assert!(result.is_ok(), "{}", input);
//         let (_, commands) = result.unwrap();

//         let mut ctx = Context::new();
//         let mut store = Store::new();
//         let mut result = None;
//         for c in commands {
//             match c {
//                 Command::Eval(t) => result = Some(t.eval(&ctx, &mut store)),
//                 Command::Bind(s, b) => {
//                     let b = b.check(&mut ctx).eval(&ctx, &mut store);
//                     ctx.add_binding(s, b);
//                     store.shift(1)
//                 }
//             }
//         }

//         assert!(result.is_some(), "{}", input);
//         let t = result.unwrap();
//         assert_eq!(expect_term, format!("{}", t), "{}", input);
//         assert_eq!(expect_ty, format!("{}", t.ty(&mut ctx)), "{}", input);
//     }
// }

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let ctx = Context::new();
    let t = TmTAbs("X".into(), box TmAbs("x".into(), TyVar(0), box TmVar(0)));

    println!("t = {:?}", t);
    println!("t.eval(...) = {:?}", t.eval(&ctx));

    Ok(())
}
