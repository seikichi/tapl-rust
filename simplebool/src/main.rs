#![feature(box_syntax, box_patterns)]

use std::env;
use std::fmt;
use std::fs;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyArr(Box<Ty>, Box<Ty>),
    TyBool,
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(usize),
    TmAbs(String, Ty, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmTrue,
    TmFalse,
    TmIf(Box<Term>, Box<Term>, Box<Term>),
}

#[derive(Debug, Clone)]
pub enum Binding {
    NameBind,
    VarBind(Ty),
}

#[derive(Debug)]
pub enum Command {
    Eval(Term),
    Bind(String, Binding),
}

use Binding::*;
use Command::*;
use Term::*;
use Ty::*;

// NOTE: Copy on Write
#[derive(Debug, Clone)]
pub struct Context {
    bindings: Vec<(String, Binding)>,
}

impl Context {
    fn new() -> Self {
        Self { bindings: vec![] }
    }

    fn add_binding(&self, x: String, bind: Binding) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.push((x, bind));
        Self { bindings }
    }

    fn add_name(&self, x: String) -> Self {
        self.add_binding(x, NameBind)
    }

    fn index2name(&self, x: usize) -> &String {
        &self.bindings[self.bindings.len() - x - 1].0
    }

    fn name2index(&self, x: &str) -> Option<usize> {
        self.bindings.iter().rev().position(|(y, _)| y == x)
    }

    fn get_binding(&self, i: usize) -> &Binding {
        &self.bindings[self.bindings.len() - i - 1].1
    }

    fn get_type(&self, i: usize) -> &Ty {
        match self.get_binding(i) {
            VarBind(ty) => ty,
            _ => panic!("Wrong kind of binding for variable"),
        }
    }

    fn add_fresh_name(&self, x: &str) -> (Self, String) {
        let mut name: String = x.into();
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        (self.add_name(name.clone()), name)
    }

    fn is_name_bound(&self, x: &str) -> bool {
        self.bindings.iter().rev().any(|(s, _)| s == x)
    }
}

impl Term {
    fn map<F: Copy + Fn(i32, usize) -> Self>(&self, c: i32, onvar: F) -> Self {
        match &self {
            TmVar(x) => onvar(c, *x),
            TmAbs(x, ty1, t2) => TmAbs(x.clone(), ty1.clone(), box t2.map(c + 1, onvar)),
            TmApp(t1, t2) => TmApp(t1.map(c, onvar).into(), t2.map(c, onvar).into()),
            TmTrue | TmFalse => (*self).clone(),
            TmIf(t1, t2, t3) => TmIf(
                box t1.map(c, onvar),
                box t2.map(c, onvar),
                box t3.map(c, onvar),
            ),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(c, |c, x| {
            if x as i32 >= c {
                TmVar((x as i32 + d) as usize)
            } else {
                TmVar(x)
            }
        })
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(j, |j, x| if x as i32 == j { s.shift(j) } else { TmVar(x) })
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn is_val(&self, _ctx: &Context) -> bool {
        match self {
            TmTrue | TmFalse | TmAbs(_, _, _) => true,
            _ => false,
        }
    }

    fn eval1(&self, ctx: &Context) -> Option<Self> {
        match self {
            TmApp(box TmAbs(_, _, t12), v2) if v2.is_val(ctx) => Some(t12.subst_top(v2)),
            TmApp(v1, t2) if v1.is_val(ctx) => Some(TmApp(v1.clone(), box t2.eval1(ctx)?)),
            TmApp(t1, t2) => Some(TmApp(box t1.eval1(ctx)?, t2.clone())),
            TmIf(box TmTrue, t2, _) => Some((**t2).clone()),
            TmIf(box TmFalse, _, t3) => Some((**t3).clone()),
            TmIf(t1, t2, t3) => Some(TmIf(box t1.eval1(ctx)?, t2.clone(), t3.clone())),
            _ => None,
        }
    }

    fn eval(&self, ctx: &Context) -> Self {
        let mut t = self.clone();
        while let Some(n) = t.eval1(ctx) {
            t = n;
        }
        t
    }

    fn ty(&self, ctx: &Context) -> Ty {
        match self {
            TmVar(i) => ctx.get_type(*i).clone(),
            TmAbs(x, ty1, t2) => {
                let ctx = ctx.add_binding(x.clone(), VarBind(ty1.clone()));
                TyArr(box ty1.clone(), box t2.ty(&ctx))
            }
            TmApp(t1, t2) => {
                let ty1 = t1.ty(ctx);
                let ty2 = t2.ty(ctx);
                match ty1 {
                    TyArr(ty11, ty12) => {
                        if ty2 == *ty11 {
                            return *ty12;
                        }
                        panic!("parameter type mismatch: {}, {}", ty2, *ty11);
                    }
                    _ => panic!("arrow type expected: {}", ty1),
                }
            }
            TmTrue | TmFalse => TyBool,
            TmIf(t1, t2, t3) => {
                if t1.ty(ctx) == TyBool {
                    let ty2 = t2.ty(ctx);
                    if ty2 == t3.ty(ctx) {
                        return ty2;
                    }
                    panic!("arms of conditional have different types");
                }
                panic!("guard of conditional not a boolean");
            }
        }
    }

    fn format(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmAbs(x, ty, t1) => {
                let (ctx, x) = ctx.add_fresh_name(x);
                write!(f, "λ {}: {}. ", x, ty)?;
                t1.format(&ctx, f)
            }
            TmIf(t1, t2, t3) => {
                write!(f, "if ")?;
                t1.format(ctx, f)?;
                write!(f, " then ")?;
                t2.format(ctx, f)?;
                write!(f, " else ")?;
                t3.format(ctx, f)
            }
            _ => self.format_app_term(ctx, f),
        }
    }

    fn format_app_term(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmApp(t1, t2) => {
                t1.format_app_term(ctx, f)?;
                write!(f, " ")?;
                t2.format_atomic_term(ctx, f)
            }
            _ => self.format_atomic_term(ctx, f),
        }
    }

    fn format_atomic_term(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmVar(x) => write!(f, "{}", ctx.index2name(*x)),
            TmTrue => write!(f, "true"),
            TmFalse => write!(f, "false"),
            _ => {
                write!(f, "(")?;
                self.format(ctx, f)?;
                write!(f, ")")
            }
        }
    }
}

impl Ty {
    fn format(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            _ => self.format_arr_ty(ctx, f),
        }
    }

    fn format_arr_ty(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyArr(t1, t2) => {
                t1.format_atomic_ty(ctx, f)?;
                write!(f, " -> ")?;
                t2.format_arr_ty(ctx, f)
            }
            _ => self.format_atomic_ty(ctx, f),
        }
    }

    fn format_atomic_ty(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyBool => write!(f, "Bool"),
            _ => {
                write!(f, "(")?;
                self.format(ctx, f)?;
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(&Context::new(), f)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(&Context::new(), f)
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameBind => Ok(()),
            VarBind(ty) => write!(f, ": {}", ty),
        }
    }
}

mod parser {
    use super::*;

    use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{
            alpha1, alphanumeric0, char, multispace0 as ms0, multispace1 as ms1,
        },
        combinator::{map, verify},
        multi::{separated_list, separated_nonempty_list},
        sequence::{delimited, pair, preceded, tuple},
        IResult,
    };

    type ParseResult<T> = Box<dyn Fn(&Context) -> T>;

    pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
        let (input, fs) = separated_list(pair(ms0, char(';')), command)(input)?;

        let mut ctx = Context::new();
        let mut commands = vec![];

        for f in fs {
            let (cmd, nctx) = f(&ctx);
            commands.push(cmd);
            ctx = nctx;
        }

        Ok((input, commands))
    }

    fn command(input: &str) -> IResult<&str, ParseResult<(Command, Context)>> {
        alt((
            map(
                pair(preceded(ms0, identifier), binder),
                |(id, f)| -> ParseResult<_> {
                    box move |ctx| (Bind(id.clone(), f(ctx)), ctx.add_name(id.clone()))
                },
            ),
            map(term, |f| -> ParseResult<_> {
                box move |ctx| (Eval(f(ctx)), (*ctx).clone())
            }),
        ))(input)
    }

    fn binder(input: &str) -> IResult<&str, ParseResult<Binding>> {
        map(
            preceded(tuple((ms0, char(':'), ms0)), all_type),
            |f| -> ParseResult<_> { box move |ctx| VarBind(f(ctx)) },
        )(input)
    }

    fn all_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
        preceded(ms0, arrow_type)(input)
    }

    fn atomic_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
        alt((
            map(tag("Bool"), |_| -> ParseResult<_> { box |_ctx| TyBool }),
            preceded(ms0, delimited(char('('), all_type, char(')'))),
        ))(input)
    }

    fn arrow_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
        map(
            separated_nonempty_list(pair(ms0, tag("->")), atomic_type),
            |fs| {
                let mut it = fs.into_iter().rev();
                let f = it.next().unwrap();
                it.fold(f, |f1, f2| box move |ctx| TyArr(box f2(ctx), box f1(ctx)))
            },
        )(input)
    }

    pub fn term(input: &str) -> IResult<&str, ParseResult<Term>> {
        alt((if_term, lambda, app_term))(input)
    }

    fn lambda(input: &str) -> IResult<&str, ParseResult<Term>> {
        map(
            tuple((
                preceded(ms0, alt((tag("lambda"), tag("λ")))),
                preceded(ms1, identifier),
                preceded(ms0, char(':')),
                all_type,
                preceded(ms0, char('.')),
                term,
            )),
            |(_, s, _, tyf, _, tf)| -> ParseResult<_> {
                box move |ctx| {
                    let ctx = ctx.add_name(s.clone());
                    TmAbs(s.clone(), tyf(&ctx), box tf(&ctx))
                }
            },
        )(input)
    }

    fn if_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        map(
            tuple((
                preceded(ms0, tag("if")),
                term,
                preceded(ms1, tag("then")),
                term,
                preceded(ms1, tag("else")),
                term,
            )),
            |(_, f1, _, f2, _, f3)| -> ParseResult<_> {
                box move |ctx| TmIf(box f1(ctx), box f2(ctx), box f3(ctx))
            },
        )(input)
    }

    fn app_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        map(separated_nonempty_list(ms1, atomic_term), |fs| {
            let mut it = fs.into_iter();
            let f = it.next().unwrap();
            it.fold(f, |f1, f2| box move |ctx| TmApp(box f1(ctx), box f2(ctx)))
        })(input)
    }

    fn atomic_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        preceded(
            ms0,
            alt((
                map(tag("true"), |_| -> ParseResult<_> { box |_| TmTrue }),
                map(tag("false"), |_| -> ParseResult<_> { box |_| TmFalse }),
                map(identifier, |s| -> ParseResult<_> {
                    box move |ctx| TmVar(ctx.name2index(&s).unwrap())
                }),
                delimited(char('('), term, char(')')),
            )),
        )(input)
    }

    const RESERVED_KEYWORDS: &'static [&'static str] = &["true", "false", "if", "then", "else"];

    fn identifier(input: &str) -> IResult<&str, String> {
        verify(
            map(pair(alpha1, alphanumeric0), |(s1, s2)| {
                format!("{}{}", s1, s2)
            }),
            |s: &String| !RESERVED_KEYWORDS.iter().any(|x| x == &s),
        )(input)
    }
}

fn process_command(commands: &[Command]) {
    let mut ctx = Context::new();
    for c in commands {
        match c {
            Command::Eval(t) => {
                println!("> {}\n{} : {}", t, t.eval(&ctx), t.ty(&ctx));
            }
            Command::Bind(s, b) => {
                println!("> {} {}", s, b);
                ctx = ctx.add_binding(s.clone(), b.clone());
            }
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let code = fs::read_to_string(filename)?;
    let (_, commands) = parser::parse(&code).unwrap();

    process_command(&commands);

    Ok(())
}
