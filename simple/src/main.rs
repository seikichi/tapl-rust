#![feature(box_syntax, box_patterns)]

use std::env;
use std::fmt;
use std::fs;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyArr(Box<Ty>, Box<Ty>),
    TyBool,
    TyNat,
    TyUnit,
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(usize),
    TmAbs(String, Ty, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmTrue,
    TmFalse,
    TmIf(Box<Term>, Box<Term>, Box<Term>),
    // Nat
    TmZero,
    TmSucc(Box<Term>),
    TmPred(Box<Term>),
    TmIsZero(Box<Term>),
    // Unit
    TmUnit,
    // Extension
    TmLet(String, Box<Term>, Box<Term>),
    TmFix(Box<Term>),
}

#[derive(Debug)]
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

#[derive(Debug)]
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
        self.bindings.push((x, bind));
        let result = f(self);
        self.bindings.pop();
        result
    }

    fn with_name<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, f: F) -> R {
        self.with_binding(x, NameBind, f)
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

    fn with_fresh_name<R, F: FnOnce(&mut Self, String) -> R>(&mut self, x: &str, f: F) -> R {
        let mut name: String = x.into();
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        self.with_name(name.clone(), move |ctx| f(ctx, name))
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
            TmApp(t1, t2) => TmApp(box t1.map(c, onvar), box t2.map(c, onvar)),
            TmTrue | TmFalse => (*self).clone(),
            TmIf(t1, t2, t3) => TmIf(
                box t1.map(c, onvar),
                box t2.map(c, onvar),
                box t3.map(c, onvar),
            ),
            // Nat
            TmZero => TmZero,
            TmSucc(t1) => TmSucc(box t1.map(c, onvar)),
            TmPred(t1) => TmPred(box t1.map(c, onvar)),
            TmIsZero(t1) => TmIsZero(box t1.map(c, onvar)),
            // Unit
            TmUnit => TmUnit,
            // Extension
            TmLet(x, t1, t2) => TmLet(x.clone(), box t1.map(c, onvar), box t2.map(c + 1, onvar)),
            TmFix(t1) => TmFix(box t1.map(c, onvar)),
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

    fn is_numeric_val(&self, ctx: &Context) -> bool {
        match self {
            TmZero => true,
            TmSucc(t1) => t1.is_numeric_val(ctx),
            _ => false,
        }
    }

    fn is_val(&self, ctx: &Context) -> bool {
        match self {
            TmTrue | TmFalse | TmAbs(_, _, _) | TmUnit => true,
            _ if self.is_numeric_val(ctx) => true,
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
            // Nat
            TmSucc(t1) => Some(TmSucc(box t1.eval1(ctx)?)),
            TmPred(box TmZero) => Some(TmZero),
            TmPred(box TmSucc(nv1)) if nv1.is_numeric_val(ctx) => Some((**nv1).clone()),
            TmPred(t1) => Some(TmPred(box t1.eval1(ctx)?)),
            TmIsZero(box TmZero) => Some(TmTrue),
            TmIsZero(box TmSucc(nv1)) if nv1.is_numeric_val(ctx) => Some(TmFalse),
            TmIsZero(t1) => Some(TmIsZero(box t1.eval1(ctx)?)),
            // Extension
            TmLet(_, v1, t2) if v1.is_val(ctx) => Some(t2.subst_top(v1)),
            TmLet(x, t1, t2) => Some(TmLet(x.clone(), box t1.eval1(ctx)?, t2.clone())),
            TmFix(box TmAbs(_, _, t12)) => Some(t12.subst_top(self)),
            TmFix(t1) if !t1.is_val(ctx) => Some(TmFix(box t1.eval1(ctx)?)),
            // Other
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

    // fn eval_by_big_step(&self, ctx: &Context) -> Self {
    //     match self {
    //         TmApp(t1, t2) => {
    //             let t1 = t1.eval(ctx);
    //             let t2 = t2.eval(ctx);
    //             if let TmAbs(_, _, t12) = &t1 {
    //                 if t2.is_val(ctx) {
    //                     return t12.subst_top(&t2);
    //                 }
    //             }
    //             TmApp(box t1, box t2)
    //         }
    //         TmIf(t1, t2, t3) => {
    //             if let TmTrue = t1.eval(ctx) {
    //                 t2.eval(ctx)
    //             } else {
    //                 t3.eval(ctx)
    //             }
    //         }
    //         _ => (*self).clone(),
    //     }
    // }

    fn ty(&self, ctx: &mut Context) -> Ty {
        match self {
            TmVar(i) => ctx.get_type(*i).clone(),
            TmAbs(x, ty1, t2) => ctx.with_binding(x.clone(), VarBind(ty1.clone()), |mut ctx| {
                TyArr(box ty1.clone(), box t2.ty(&mut ctx))
            }),
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
            // Unit
            TmUnit => TyUnit,
            // Nat
            TmZero => TyNat,
            TmSucc(t1) => {
                if let TyNat = t1.ty(ctx) {
                    return TyNat;
                }
                panic!("argument of succ is not a number");
            }
            TmPred(t1) => {
                if let TyNat = t1.ty(ctx) {
                    return TyNat;
                }
                panic!("argument of succ is not a number");
            }
            TmIsZero(t1) => {
                if let TyNat = t1.ty(ctx) {
                    return TyBool;
                }
                panic!("argument of succ is not a number");
            }
            // Extension
            TmLet(x, t1, t2) => {
                let ty1 = t1.ty(ctx);
                ctx.with_binding(x.clone(), VarBind(ty1), |ctx| t2.ty(ctx))
            }
            TmFix(t1) => {
                if let TyArr(box ty11, box ty12) = t1.ty(ctx) {
                    if ty11 == ty12 {
                        return ty12.clone();
                    }
                    panic!("result of body not compatible");
                }
                panic!("arrow type expected");
            }
        }
    }

    fn format(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmAbs(x, ty, t1) => ctx.with_fresh_name(x, |mut ctx, x| {
                write!(f, "λ {}: {}. ", x, ty)?;
                t1.format(&mut ctx, f)
            }),
            TmIf(t1, t2, t3) => {
                write!(f, "if ")?;
                t1.format(ctx, f)?;
                write!(f, " then ")?;
                t2.format(ctx, f)?;
                write!(f, " else ")?;
                t3.format(ctx, f)
            }
            TmLet(x, t1, t2) => {
                write!(f, "let {} = ", x)?;
                t1.format(ctx, f)?;
                write!(f, " in ")?;
                t2.format(ctx, f)
            }
            TmFix(t1) => {
                write!(f, "fix ")?;
                t1.format(ctx, f)
            }
            _ => self.format_app_term(ctx, f),
        }
    }

    fn format_app_term(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmApp(t1, t2) => {
                t1.format_app_term(ctx, f)?;
                write!(f, " ")?;
                t2.format_atomic_term(ctx, f)
            }
            // Nat
            TmPred(t1) => {
                write!(f, "pred ")?;
                t1.format_app_term(ctx, f)
            }
            TmIsZero(t1) => {
                write!(f, "iszero ")?;
                t1.format_app_term(ctx, f)
            }
            _ => self.format_atomic_term(ctx, f),
        }
    }

    fn format_atomic_term(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmVar(x) => write!(f, "{}", ctx.index2name(*x)),
            TmTrue => write!(f, "true"),
            TmFalse => write!(f, "false"),
            TmUnit => write!(f, "unit"),
            TmZero => write!(f, "0"),
            TmSucc(t1) => {
                let mut t = t1;
                let mut n = 1;
                loop {
                    match t {
                        box TmZero => return write!(f, "{}", n),
                        box TmSucc(s) => {
                            t = s;
                            n += 1;
                        }
                        _ => {
                            return {
                                write!(f, "(succ ")?;
                                t1.format_atomic_term(ctx, f)?;
                                write!(f, ")")
                            }
                        }
                    }
                }
            }
            _ => {
                write!(f, "(")?;
                self.format(ctx, f)?;
                write!(f, ")")
            }
        }
    }
}

impl Ty {
    fn format(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            _ => self.format_arr_ty(ctx, f),
        }
    }

    fn format_arr_ty(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyArr(t1, t2) => {
                t1.format_atomic_ty(ctx, f)?;
                write!(f, " -> ")?;
                t2.format_arr_ty(ctx, f)
            }
            _ => self.format_atomic_ty(ctx, f),
        }
    }

    fn format_atomic_ty(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyBool => write!(f, "Bool"),
            TyUnit => write!(f, "Unit"),
            TyNat => write!(f, "Nat"),
            TyArr(_, _) => {
                write!(f, "(")?;
                self.format(ctx, f)?;
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(&mut Context::new(), f)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(&mut Context::new(), f)
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
            alpha1, alphanumeric0, char, digit1, multispace0 as ms0, multispace1 as ms1,
        },
        combinator::{map, verify},
        multi::{separated_list, separated_nonempty_list},
        sequence::{delimited, pair, preceded, tuple},
        IResult,
    };

    type ParseResult<T> = Box<dyn Fn(&mut Context) -> T>;

    pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
        map(separated_list(pair(ms0, char(';')), command), |fs| {
            let mut ctx = Context::new();
            fs.iter().map(|f| f(&mut ctx)).collect()
        })(input)
    }

    fn command(input: &str) -> IResult<&str, ParseResult<Command>> {
        alt((
            map(
                pair(preceded(ms0, identifier), binder),
                |(id, f)| -> ParseResult<_> {
                    box move |ctx| {
                        ctx.add_name(id.clone());
                        Bind(id.clone(), f(ctx))
                    }
                },
            ),
            map(term, |f| -> ParseResult<_> { box move |ctx| Eval(f(ctx)) }),
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
            map(preceded(ms0, tag("Bool")), |_| -> ParseResult<_> {
                box |_ctx| TyBool
            }),
            map(preceded(ms0, tag("Unit")), |_| -> ParseResult<_> {
                box |_ctx| TyUnit
            }),
            map(preceded(ms0, tag("Nat")), |_| -> ParseResult<_> {
                box |_ctx| TyNat
            }),
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
        alt((if_term, lambda, let_term, letrec_term, app_term))(input)
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
                    ctx.with_name(s.clone(), |mut ctx| {
                        TmAbs(s.clone(), tyf(&mut ctx), box tf(&mut ctx))
                    })
                }
            },
        )(input)
    }

    fn let_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        map(
            tuple((
                preceded(ms0, tag("let")),
                preceded(ms1, identifier),
                preceded(ms0, char('=')),
                term,
                preceded(ms1, tag("in")),
                preceded(ms1, term),
            )),
            |(_, s, _, f1, _, f2)| -> ParseResult<_> {
                box move |ctx| {
                    let t1 = f1(ctx);
                    ctx.with_name(s.clone(), |ctx| TmLet(s.clone(), box t1, box f2(ctx)))
                }
            },
        )(input)
    }

    fn letrec_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        map(
            tuple((
                preceded(ms0, tag("letrec")),
                preceded(ms1, identifier),
                preceded(ms0, char(':')),
                preceded(ms0, all_type),
                preceded(ms0, char('=')),
                term,
                preceded(ms1, tag("in")),
                preceded(ms1, term),
            )),
            |(_, s, _, fty, _, f1, _, f2)| -> ParseResult<_> {
                box move |ctx| {
                    let ty = fty(ctx);
                    ctx.with_name(s.clone(), |ctx| {
                        TmLet(
                            s.clone(),
                            box TmFix(box TmAbs(s.clone(), ty, box f1(ctx))),
                            box f2(ctx),
                        )
                    })
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
        map(separated_nonempty_list(ms1, app_term_1), |fs| {
            let mut it = fs.into_iter();
            let f = it.next().unwrap();
            it.fold(f, |f1, f2| box move |ctx| TmApp(box f1(ctx), box f2(ctx)))
        })(input)
    }

    fn app_term_1(input: &str) -> IResult<&str, ParseResult<Term>> {
        alt((
            map(
                preceded(pair(ms0, tag("fix")), atomic_term),
                |f| -> ParseResult<_> { box move |ctx| TmFix(box f(ctx)) },
            ),
            map(
                preceded(pair(ms0, tag("succ")), atomic_term),
                |f| -> ParseResult<_> { box move |ctx| TmSucc(box f(ctx)) },
            ),
            map(
                preceded(pair(ms0, tag("pred")), atomic_term),
                |f| -> ParseResult<_> { box move |ctx| TmPred(box f(ctx)) },
            ),
            map(
                preceded(pair(ms0, tag("iszero")), atomic_term),
                |f| -> ParseResult<_> { box move |ctx| TmIsZero(box f(ctx)) },
            ),
            atomic_term,
        ))(input)
    }

    fn atomic_term(input: &str) -> IResult<&str, ParseResult<Term>> {
        preceded(
            ms0,
            alt((
                map(tag("true"), |_| -> ParseResult<_> { box |_| TmTrue }),
                map(tag("false"), |_| -> ParseResult<_> { box |_| TmFalse }),
                map(tag("unit"), |_| -> ParseResult<_> { box |_| TmUnit }),
                map(identifier, |s| -> ParseResult<_> {
                    box move |ctx| TmVar(ctx.name2index(&s).unwrap())
                }),
                delimited(char('('), term, char(')')),
                // Nat
                map(int_value, |n| -> ParseResult<_> {
                    box move |_| {
                        let mut result = TmZero;
                        for _ in 0..n {
                            result = TmSucc(box result);
                        }
                        result
                    }
                }),
            )),
        )(input)
    }

    const RESERVED_KEYWORDS: &'static [&'static str] = &[
        "true", "false", "if", "then", "else", "succ", "pred", "iszero", "let", "in", "fix", "unit",
    ];

    fn identifier(input: &str) -> IResult<&str, String> {
        verify(
            map(pair(alpha1, alphanumeric0), |(s1, s2)| {
                format!("{}{}", s1, s2)
            }),
            |s: &String| !RESERVED_KEYWORDS.iter().any(|x| x == &s),
        )(input)
    }

    fn int_value(input: &str) -> IResult<&str, u32> {
        map(digit1, |s: &str| s.parse().unwrap())(input)
    }
}

#[test]
fn test() {
    let testcases = vec![
        // Bool,
        ("true", "true", "Bool"),
        (
            "(λ x: Bool -> Bool. if x true then true else false) (λ x: Bool. x)",
            "true",
            "Bool",
        ),
        (
            "(λ x: Bool -> Bool -> Bool. x true false) (λ x: Bool. λ y: Bool. true)",
            "true",
            "Bool",
        ),
        // Unit
        ("unit", "unit", "Unit"),
        ("λ x: Bool. unit", "λ x: Bool. unit", "Bool -> Unit"),
        ("(λ x: Bool. unit) true", "unit", "Unit"),
        // Nat
        ("(λ x: Nat. succ x) 41", "42", "Nat"),
        ("(λ x: Nat. if iszero x then 42 else 0) 0", "42", "Nat"),
        ("(λ x: Nat. if iszero x then 42 else 0) 1", "0", "Nat"),
        // Let
        ("let x=true in x", "true", "Bool"),
        ("let x=0 in let f=λ x: Nat. succ x in f x", "1", "Nat"),
        // Fix
        (
            "(fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then n else succ (f (pred m) n))) 40 2",
            "42",
            "Nat",
        ),
        // Letrec
        (
            "
            letrec plus: Nat -> Nat -> Nat =
              λ m: Nat. λ n: Nat.
                if iszero m then n else succ (plus (pred m) n) in
            letrec times: Nat -> Nat -> Nat =
              λ m: Nat. λ n: Nat.
                if iszero m then 0 else plus n (times (pred m) n) in
            letrec factorial: Nat -> Nat =
              λ m: Nat.
                if iszero m then 1 else times m (factorial (pred m)) in
            factorial 5
            ",
            "120",
            "Nat",
        )
    ];

    for (input, expect_term, expect_ty) in testcases {
        let (_, commands) = parser::parse(input).unwrap();

        let mut ctx = Context::new();
        let mut result = None;
        for c in commands {
            match c {
                Command::Eval(t) => result = Some(t.eval(&ctx)),
                Command::Bind(s, b) => ctx.add_binding(s, b),
            }
        }

        let t = result.unwrap();
        assert_eq!(expect_term, format!("{}", t), "{}", input);
        assert_eq!(expect_ty, format!("{}", t.ty(&mut ctx)), "{}", input);
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let code = fs::read_to_string(filename)?;
    let (_, commands) = parser::parse(&code).unwrap();

    let mut ctx = Context::new();
    for c in commands {
        match c {
            Command::Eval(t) => {
                println!("> {}", t);
                println!("{} : {}", t.eval(&ctx), t.ty(&mut ctx));
            }
            Command::Bind(s, b) => {
                println!("> {} {}", s, b);
                ctx.add_binding(s, b);
            }
        }
    }

    Ok(())
}
