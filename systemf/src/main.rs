#![feature(box_syntax, box_patterns)]

use std::env;
use std::fmt;
use std::fs;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyVar(Rc<str>, usize),
    TyArr(Box<Ty>, Box<Ty>),
    TyAll(Rc<str>, Box<Ty>),
    TySome(Rc<str>, Box<Ty>),
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(Rc<str>, usize),
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

    fn is_tyabb(&self, i: usize) -> bool {
        match self.get_binding(i) {
            TyAbbBind(ty) => true,
            _ => false,
        }
    }

    fn get_tyabb(&self, i: usize) -> Ty {
        match self.get_binding(i) {
            TyAbbBind(ty) => ty,
            _ => panic!("No TyAbbBind"),
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
    fn map<F: Copy + Fn(i32, Rc<str>, usize) -> Self, TF: Copy + Fn(i32, &Ty) -> Ty>(
        &self,
        c: i32,
        onvar: F,
        ontype: TF,
    ) -> Self {
        match &self {
            TmVar(n, x) => onvar(c, n.clone(), *x),
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
            |c, n, x| {
                if x as i32 >= c {
                    TmVar(n, (x as i32 + d) as usize)
                } else {
                    TmVar(n, x)
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
            |j, n, x| {
                if x as i32 == j {
                    s.shift(j)
                } else {
                    TmVar(n, x)
                }
            },
            |_, ty| ty.clone(),
        )
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn ty_subst(&self, j: i32, ty: &Ty) -> Self {
        self.map(j, |_, n, x| TmVar(n, x), |j, ty2| ty2.subst(j, ty))
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
            TmVar(_, n) => match ctx.get_binding(*n) {
                TmAbbBind(t, _) => t.clone(),
                _ => return None,
            },
            // TmTApp
            TmTApp(box TmTAbs(_, t11), ty2) => t11.ty_subst_top(ty2),
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

    fn ty(&self, ctx: &mut Context) -> Ty {
        match self {
            TmVar(_, i) => ctx.get_type(*i),
            TmAbs(x, tyt1, t2) => ctx.with_binding(x.to_string(), VarBind(tyt1.clone()), |ctx| {
                let tyt2 = t2.ty(ctx);
                TyArr(box tyt1.clone(), box tyt2.shift(-1))
            }),
            TmApp(t1, t2) => {
                let tyt1 = t1.ty(ctx);
                let tyt2 = t2.ty(ctx);
                match tyt1.simplify(ctx) {
                    TyArr(box tyt11, box tyt12) if tyt2.eqv(&tyt11, ctx) => tyt12,
                    TyArr(_, _) => panic!("parameter type mismatch"),
                    _ => panic!("arrow type expected"),
                }
            }
            TmTAbs(tyx, t2) => ctx.with_binding(tyx.to_string(), TyVarBind, |ctx| {
                let tyt2 = t2.ty(ctx);
                TyAll(tyx.clone(), box tyt2)
            }),
            TmTApp(t1, tyt2) => {
                let tyt1 = t1.ty(ctx);
                match tyt1.simplify(ctx) {
                    TyAll(_, tyt12) => tyt12.subst_top(tyt2),
                    _ => panic!("universal type expected"),
                }
            }
            _ => panic!("unimplemented"), // TODO
        }
    }

    fn fix(&mut self, ctx: &mut Context) {
        match self {
            TmVar(s, x) => *x = ctx.name2index(s).unwrap(),
            TmAbs(s, ty, t) => {
                ty.fix(ctx);
                ctx.with_name(s.to_string(), |ctx| t.fix(ctx))
            }
            TmApp(t1, t2) => {
                t1.fix(ctx);
                t2.fix(ctx)
            }
            TmTAbs(s, t) => ctx.with_name(s.to_string(), |ctx| t.fix(ctx)),
            TmTApp(t, ty) => {
                t.fix(ctx);
                ty.fix(ctx)
            }
            TmPack(ty1, t2, ty3) => {
                ty1.fix(ctx);
                t2.fix(ctx);
                ty3.fix(ctx);
            }
            TmUnpack(s1, s2, t1, t2) => {
                t1.fix(ctx);
                ctx.with_name(s1.to_string(), |ctx| {
                    ctx.with_name(s2.to_string(), |ctx| t2.fix(ctx))
                })
            }
        }
    }
}

impl Ty {
    fn map<F: Copy + Fn(i32, Rc<str>, usize) -> Self>(&self, c: i32, onvar: F) -> Self {
        match &self {
            TyVar(s, x) => onvar(c, s.clone(), *x),
            TyArr(ty1, ty2) => TyArr(box ty1.map(c, onvar), box ty2.map(c, onvar)),
            TyAll(tyx, ty2) => TyAll(tyx.clone(), box ty2.map(c + 1, onvar)),
            TySome(tyx, ty2) => TySome(tyx.clone(), box ty2.map(c + 1, onvar)),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(c, |c, s, x| {
            if x as i32 >= c {
                TyVar(s, (x as i32 + d) as usize)
            } else {
                TyVar(s, x)
            }
        })
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(j, |j, n, x| {
            if x as i32 == j {
                s.shift(j)
            } else {
                TyVar(n, x)
            }
        })
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn compute(&self, ctx: &Context) -> Option<Self> {
        match self {
            TyVar(_, i) if ctx.is_tyabb(*i) => Some(ctx.get_tyabb(*i)),
            _ => None,
        }
    }

    fn simplify(&self, ctx: &Context) -> Self {
        let mut ty = self.clone();
        while let Some(next) = ty.compute(ctx) {
            ty = next;
        }
        ty
    }

    fn eqv(&self, rhs: &Ty, ctx: &mut Context) -> bool {
        let tys = self.simplify(ctx);
        let tyt = rhs.simplify(ctx);

        match (&tys, &tyt) {
            (TyVar(_, i), _) if ctx.is_tyabb(*i) => ctx.get_tyabb(*i).eqv(&tyt, ctx),
            (_, TyVar(_, i)) if ctx.is_tyabb(*i) => tys.eqv(&ctx.get_tyabb(*i), ctx),
            (TyVar(_, i), TyVar(_, j)) => i == j,
            (TyArr(tys1, tys2), TyArr(tyt1, tyt2)) => tys1.eqv(&tyt1, ctx) && tys2.eqv(&tyt2, ctx),
            (TySome(tyx1, tys2), TySome(_, tyt2)) => {
                ctx.with_name(tyx1.to_string(), |ctx| tys2.eqv(&tyt2, ctx))
            }
            (TyAll(tyx1, tys2), TyAll(_, tyt2)) => {
                ctx.with_name(tyx1.to_string(), |ctx| tys2.eqv(&tyt2, ctx))
            }
            _ => false,
        }
    }

    fn fix(&mut self, ctx: &mut Context) {
        match self {
            TyVar(s, n) => *n = ctx.name2index(s).unwrap(),
            TyArr(ty1, ty2) => {
                ty1.fix(ctx);
                ty2.fix(ctx);
            }
            TyAll(s, ty) => ctx.with_name(s.to_string(), |ctx| ty.fix(ctx)),
            TySome(s, ty) => ctx.with_name(s.to_string(), |ctx| ty.fix(ctx)),
        }
    }

    fn format(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyAll(tyx, tyt2) => {
                write!(f, "∀{}. ", tyx)?;
                tyt2.format(f)
            }
            _ => self.format_arrow(f),
        }
    }

    fn format_arrow(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyArr(tyt1, tyt2) => {
                tyt1.format(f)?;
                write!(f, " -> ")?;
                tyt2.format(f)
            }
            _ => self.format_atomic(f),
        }
    }

    fn format_atomic(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyVar(s, _) => write!(f, "{}", s),
            TySome(tyx, tyt2) => {
                write!(f, "{{∃{}, ", tyx)?;
                tyt2.format(f)?;
                write!(f, "}}")
            }
            _ => {
                write!(f, "(")?;
                self.format(f)?;
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f)
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

    fn eval(&self, ctx: &Context) -> Self {
        match &self {
            TmAbbBind(t, ty) => TmAbbBind(t.eval(ctx), ty.clone()),
            _ => self.clone(), // FIXME
        }
    }

    fn fix(&mut self, ctx: &mut Context) {
        match self {
            NameBind => {}
            VarBind(ty) => ty.fix(ctx),
            TyVarBind => {}
            TyAbbBind(ty) => ty.fix(ctx),
            TmAbbBind(t, None) => t.fix(ctx),
            TmAbbBind(t, Some(ty)) => {
                t.fix(ctx);
                ty.fix(ctx);
            }
        }
    }
}

impl Command {
    fn fix(&mut self, ctx: &mut Context) {
        match self {
            Eval(t) => t.fix(ctx),
            Bind(s, b) => {
                b.fix(ctx);
                ctx.add_name(s.to_string())
            }
            SomeBind(s1, s2, t) => {
                t.fix(ctx);
                ctx.add_name(s1.to_string());
                ctx.add_name(s2.to_string());
            }
        }
    }
}

mod parser {
    use super::*;

    use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{
            alpha1, alphanumeric0, char, digit1, multispace0 as ms0, multispace1 as ms1, none_of,
            one_of,
        },
        combinator::{map, not, peek, recognize, verify},
        multi::{many0, many1, separated_list, separated_nonempty_list},
        number::complete::double,
        sequence::{delimited, pair, preceded, terminated, tuple},
        IResult,
    };

    // tokens
    const id_chars: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";

    fn id(input: &str) -> IResult<&str, Rc<str>> {
        map(
            preceded(ms0, recognize(many1(one_of(id_chars)))),
            |s: &str| s.into(),
        )(input)
    }

    fn ucid(input: &str) -> IResult<&str, Rc<str>> {
        verify(id, |id: &str| id.chars().next().unwrap().is_uppercase())(input)
    }

    fn lcid(input: &str) -> IResult<&str, Rc<str>> {
        verify(id, |id: &str| id.chars().next().unwrap().is_lowercase())(input)
    }

    fn lambda(input: &str) -> IResult<&str, char> {
        preceded(
            ms0,
            alt((map(pair(tag("lambda"), ms1), |_| 'λ'), char('λ'))),
        )(input)
    }

    fn s(s: &'static str) -> Box<dyn Fn(&str) -> IResult<&str, ()>> {
        box move |input: &str| map(preceded(ms0, tag(s)), |_| {})(input)
    }

    // parsers
    pub fn term(input: &str) -> IResult<&str, Term> {
        alt((app_term, lambda_term))(input) // FIXME
    }

    fn lambda_term(input: &str) -> IResult<&str, Term> {
        alt((
            map(
                tuple((lambda, lcid, s(":"), ty, s("."), term)),
                |(_, id, _, ty, _, t)| TmAbs(id.clone(), ty, box t),
            ),
            map(
                tuple((lambda, s("_"), s(":"), ty, s("."), term)),
                |(_, _, _, ty, _, t)| TmAbs("_".into(), ty, box t),
            ),
            map(tuple((lambda, ucid, s("."), term)), |(_, id, _, t)| {
                TmTAbs(id, box t)
            }),
        ))(input)
    }

    fn app_term(input: &str) -> IResult<&str, Term> {
        map(
            pair(app_term_head, separated_list(ms1, app_term_rest)),
            |(head, tail)| tail.iter().fold(head, |t, f| f(t)),
        )(input)
    }

    fn app_term_head(input: &str) -> IResult<&str, Term> {
        atomic_term(input)
    }

    fn app_term_rest(input: &str) -> IResult<&str, Box<dyn Fn(Term) -> Term>> {
        alt((
            map(atomic_term, |t1| -> Box<dyn Fn(Term) -> Term> {
                box move |t2| TmApp(box t2, box t1.clone())
            }),
            map(
                delimited(s("["), ty, s("]")),
                |ty| -> Box<dyn Fn(Term) -> Term> { box move |t| TmTApp(box t, ty.clone()) },
            ),
        ))(input)
    }

    fn atomic_term(input: &str) -> IResult<&str, Term> {
        alt((
            delimited(s("("), term, s(")")),
            map(lcid, |id| TmVar(id, 0)),
        ))(input)
    }

    fn ty(input: &str) -> IResult<&str, Ty> {
        alt((
            arrow_type,
            map(tuple((s("∀"), ucid, s("."), ty)), |(_, id, _, t)| {
                TyAll(id, box t)
            }),
        ))(input)
    }

    fn arrow_type(input: &str) -> IResult<&str, Ty> {
        alt((
            map(
                tuple((atomic_type, s("->"), arrow_type)),
                |(ty1, _, ty2)| TyArr(box ty1, box ty2),
            ),
            atomic_type,
        ))(input)
    }

    fn atomic_type(input: &str) -> IResult<&str, Ty> {
        alt((
            delimited(s("("), ty, s(")")),
            map(ucid, |id| TyVar(id.into(), 0)),
            map(
                tuple((s("{"), s("∃"), ucid, s(","), ty, s("}"))),
                |(_, _, id, _, t, _)| TySome(id.into(), box t),
            ),
        ))(input)
    }

    fn binder(input: &str) -> IResult<&str, Binding> {
        alt((
            map(preceded(s(":"), ty), |ty| VarBind(ty)),
            map(preceded(s("="), term), |t| TmAbbBind(t, None)),
        ))(input)
    }

    fn ty_binder(input: &str) -> IResult<&str, Binding> {
        map(preceded(s("="), ty), |ty| TyAbbBind(ty))(input)
    }

    fn command(input: &str) -> IResult<&str, Command> {
        alt((
            map(pair(ucid, ty_binder), |(id, b)| Bind(id, b)),
            map(pair(lcid, binder), |(id, b)| Bind(id, b)),
            map(term, |t| Eval(t)),
        ))(input)
    }

    pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
        let (input, mut commands) = separated_list(s(";"), command)(input)?;
        let mut ctx = Context::new();
        for cmd in &mut commands {
            cmd.fix(&mut ctx);
        }
        Ok((input, commands))
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (_, cmds) = parser::parse(
        "
        CBool = ∀X. X -> X -> X;
        tru = λX. λt:X. λf:X. t;
        fls = λX. λt:X. λf:X. f;

        not = λb:CBool. λX. λt:X. λf:X. b [X] f t;
        not tru [CBool] tru fls;

        and = λb:CBool. λc:CBool. λX. λt:X. λf:X. b [X] (c [X] t f) f;
        and tru tru [CBool] tru fls;
        and tru fls [CBool] tru fls;
        and tru fls [CBool];

        id = λX. λx:X. x;
        not;
        id [CBool] tru;
        ",
    )
    .unwrap();

    // println!("cmds = {:?}", cmds);

    // eval loop
    let mut ctx = Context::new();
    for cmd in cmds {
        println!("> {:?}", cmd);

        match cmd {
            Eval(t) => {
                let t = t.eval(&ctx);
                let ty = t.ty(&mut ctx);
                println!("{:?}: {}", t, ty);
            }
            Bind(x, bind) => {
                let bind = bind.eval(&ctx);
                println!("{:?}", bind);
                ctx.add_binding(x.to_string(), bind);
            }
            _ => panic!("Invalid Command: {:?}", cmd),
        }
    }

    Ok(())
}
