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
        self.map(j, |_, x| TmVar(x), |j, ty2| ty2.subst(j, ty))
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
            TmVar(i) => ctx.get_type(*i),
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

    fn compute(&self, ctx: &Context) -> Option<Self> {
        match self {
            TyVar(i) if ctx.is_tyabb(*i) => Some(ctx.get_tyabb(*i)),
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
            (TyVar(i), _) if ctx.is_tyabb(*i) => ctx.get_tyabb(*i).eqv(&tyt, ctx),
            (_, TyVar(i)) if ctx.is_tyabb(*i) => tys.eqv(&ctx.get_tyabb(*i), ctx),
            (TyVar(i), TyVar(j)) => i == j,
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

    fn format(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyAll(tyx, tyt2) => ctx.with_fresh_name(&tyx, |ctx, n| {
                write!(f, "∀{}. ", n)?;
                tyt2.format(ctx, f)
            }),
            _ => self.format_arrow(ctx, f),
        }
    }

    fn format_arrow(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyArr(tyt1, tyt2) => {
                tyt1.format(ctx, f)?;
                write!(f, " -> ")?;
                tyt2.format(ctx, f)
            }
            _ => self.format_atomic(ctx, f),
        }
    }

    fn format_atomic(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyVar(x) => write!(f, "{}", ctx.index2name(*x).unwrap()),
            TySome(tyx, tyt2) => {
                write!(f, "{{∃{}, ", tyx)?;
                tyt2.format(ctx, f)?;
                write!(f, "}}")
            }
            _ => {
                write!(f, "(")?;
                self.format(ctx, f)?;
                write!(f, ")")
            }
        }
    }

    fn display(&self, ctx: &Context) -> TyDisplay {
        TyDisplay {
            ty: self.clone(),
            ctx: ctx.clone(),
        }
    }
}

struct TyDisplay {
    ty: Ty,
    ctx: Context,
}

impl fmt::Display for TyDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ty.format(&mut self.ctx.clone(), f)
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

    type ParseResult<T> = Box<dyn Fn(&mut Context) -> T>;

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

    fn colon(input: &str) -> IResult<&str, char> {
        preceded(ms0, char(':'))(input)
    }

    fn dot(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('.'))(input)
    }

    fn all(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('∀'))(input)
    }

    fn some(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('∃'))(input)
    }

    fn comma(input: &str) -> IResult<&str, char> {
        preceded(ms0, char(','))(input)
    }

    fn semi(input: &str) -> IResult<&str, char> {
        preceded(ms0, char(';'))(input)
    }

    fn eq(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('='))(input)
    }

    fn lcurly(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('{'))(input)
    }

    fn rcurly(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('}'))(input)
    }

    fn lparen(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('('))(input)
    }

    fn rparen(input: &str) -> IResult<&str, char> {
        preceded(ms0, char(')'))(input)
    }

    fn lsquare(input: &str) -> IResult<&str, char> {
        preceded(ms0, char('['))(input)
    }

    fn rsquare(input: &str) -> IResult<&str, char> {
        preceded(ms0, char(']'))(input)
    }

    // parsers
    pub fn term(input: &str) -> IResult<&str, ParseResult<Term>> {
        alt((app_term, lambda_term))(input) // FIXME
    }

    fn lambda_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        alt((
            map(
                tuple((lambda, lcid, colon, ty, dot, term)),
                |(_, id, _, fty, _, ft)| -> ParseResult<Term> {
                    box move |ctx| {
                        let ty = fty(ctx);
                        ctx.with_name(id.to_string(), |ctx| TmAbs(id.clone(), ty, box ft(ctx)))
                    }
                },
            ),
            map(
                tuple((lambda, char('_'), colon, ty, dot, term)),
                |(_, _, _, fty, _, ft)| -> ParseResult<Term> {
                    box move |ctx| {
                        let ty = fty(ctx);
                        ctx.with_name("_".into(), |ctx| TmAbs("_".into(), ty, box ft(ctx)))
                    }
                },
            ),
            map(
                tuple((lambda, ucid, dot, term)),
                |(_, id, _, ft)| -> ParseResult<Term> {
                    box move |ctx| {
                        ctx.with_name(id.to_string(), |ctx| TmTAbs(id.clone(), box ft(ctx)))
                    }
                },
            ),
        ))(input)
    }

    fn app_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        map(
            pair(app_term_head, separated_list(ms1, app_term_rest)),
            |(head, tail)| -> ParseResult<Term> {
                box move |ctx| tail.iter().fold(head(ctx), |t, f| f(ctx, t))
            },
        )(input)
    }

    fn app_term_head(input: &str) -> IResult<&str, ParseResult<Term>> {
        atomic_term(input)
    }

    fn app_term_rest(input: &str) -> IResult<&str, Box<dyn Fn(&mut Context, Term) -> Term>> {
        alt((
            map(
                atomic_term,
                |f| -> Box<dyn Fn(&mut Context, Term) -> Term> {
                    box move |ctx, t| TmApp(box t, box f(ctx))
                },
            ),
            map(
                delimited(lsquare, ty, rsquare),
                |fty| -> Box<dyn Fn(&mut Context, Term) -> Term> {
                    box move |ctx, t| TmTApp(box t, fty(ctx))
                },
            ),
        ))(input)
    }

    fn atomic_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        preceded(
            ms0,
            alt((
                delimited(lparen, term, rparen),
                map(lcid, |id| -> ParseResult<_> {
                    box move |ctx| TmVar(ctx.name2index(&id).expect(&format!("{} not found", id)))
                }),
            )),
        )(input)
    }

    fn ty(input: &str) -> IResult<&str, ParseResult<Ty>> {
        alt((
            arrow_type,
            map(
                tuple((all, ucid, dot, ty)),
                |(_, id, _, fty)| -> ParseResult<Ty> {
                    box move |ctx| {
                        ctx.with_name(id.to_string(), |ctx| TyAll(id.clone(), box fty(ctx)))
                    }
                },
            ),
        ))(input)
    }

    fn arrow_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
        alt((
            map(
                tuple((atomic_type, pair(ms0, tag("->")), arrow_type)),
                |(f1, _, f2)| -> ParseResult<Ty> { box move |ctx| TyArr(box f1(ctx), box f2(ctx)) },
            ),
            atomic_type,
        ))(input)
    }

    fn atomic_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
        preceded(
            ms0,
            alt((
                delimited(lparen, ty, rparen),
                map(ucid, |id| -> ParseResult<Ty> {
                    box move |ctx| {
                        if ctx.is_name_bound(&id) {
                            TyVar(ctx.name2index(&id).unwrap()) // TODO
                        } else {
                            panic!("NO {} Type!", id); // TODO
                        }
                    }
                }),
                map(
                    tuple((pair(lcurly, some), ucid, comma, ty, rcurly)),
                    |(_, id, _, fty, _)| -> ParseResult<Ty> {
                        box move |ctx| {
                            ctx.with_name(id.to_string(), |ctx| TySome(id.clone(), box fty(ctx)))
                        }
                    },
                ),
            )),
        )(input)
    }

    fn binder(input: &str) -> IResult<&str, ParseResult<Binding>> {
        alt((
            map(preceded(colon, ty), |fty| -> ParseResult<_> {
                box move |ctx| VarBind(fty(ctx))
            }),
            map(preceded(eq, term), |ft| -> ParseResult<_> {
                box move |ctx| TmAbbBind(ft(ctx), None)
            }),
        ))(input)
    }

    fn ty_binder(input: &str) -> IResult<&str, ParseResult<Binding>> {
        map(preceded(eq, ty), |fty| -> ParseResult<_> {
            box move |ctx| TyAbbBind(fty(ctx))
        })(input)
    }

    fn command(input: &str) -> IResult<&str, ParseResult<Command>> {
        alt((
            map(pair(ucid, ty_binder), |(id, fb)| -> ParseResult<_> {
                box move |ctx| {
                    let result = Bind(id.clone(), fb(ctx));
                    ctx.add_name(id.to_string());
                    result
                }
            }),
            map(pair(lcid, binder), |(id, fb)| -> ParseResult<_> {
                box move |ctx| {
                    let result = Bind(id.clone(), fb(ctx));
                    ctx.add_name(id.to_string());
                    result
                }
            }),
            map(term, |ft| -> ParseResult<_> {
                box move |ctx| Eval(ft(ctx))
            }),
        ))(input)
    }

    pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
        let mut ctx = Context::new();
        let (input, fs) = separated_list(semi, command)(input)?;
        let mut result = vec![];
        for f in fs {
            result.push(f(&mut ctx));
        }
        Ok((input, result))
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
                println!("{:?}: {}", t, ty.display(&ctx));
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
