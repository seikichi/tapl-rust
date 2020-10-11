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
                        ctx.with_name(id.to_string(), |ctx| {
                            TmAbs(id.clone(), fty(ctx), box ft(ctx))
                        })
                    }
                },
            ),
            map(
                tuple((lambda, char('_'), colon, ty, dot, term)),
                |(_, _, _, fty, _, ft)| -> ParseResult<Term> {
                    box move |ctx| {
                        ctx.with_name("_".into(), |ctx| TmAbs("_".into(), fty(ctx), box ft(ctx)))
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
                    tuple((pair(lcurly, some), ucid, comma, ty, rparen)),
                    |(_, id, _, fty, _)| -> ParseResult<Ty> {
                        box move |ctx| {
                            ctx.with_name(id.to_string(), |ctx| TySome(id.clone(), box fty(ctx)))
                        }
                    },
                ),
            )),
        )(input)
    }

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
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut ctx = Context::new();
    let (_, ft) = parser::term("(λX. λx:X. x) [∀X. X -> X] (λX. λx:X. x)").unwrap();
    let t = ft(&mut ctx);

    println!("t = {:?}", t);
    println!("t.eval(...) = {:?}", t.eval(&ctx));

    Ok(())
}
