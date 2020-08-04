use std::borrow::Borrow;
use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, multispace1},
    combinator::{flat_map, map, map_opt},
    multi::fold_many0,
    sequence::{delimited, tuple},
    IResult,
};

#[derive(Debug, PartialEq)]
enum Term {
    Var(i32),
    Abs(Rc<Term>),
    App(Rc<Term>, Rc<Term>),
}

#[derive(Debug)]
enum Context {
    Cons(String, Rc<Context>),
    Nil,
}

impl Context {
    fn new() -> Rc<Self> {
        Rc::new(Context::Nil)
    }

    fn with(self: &Rc<Context>, x: String) -> Rc<Self> {
        Rc::new(Context::Cons(x, self.clone()))
    }

    fn index<T: Borrow<str>>(self: &Rc<Context>, x: T) -> Option<i32> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons(car, cdr) = &*next {
            if car == x.borrow() {
                return Some(i);
            }
            i += 1;
            next = cdr.clone();
        }
        None
    }
}

fn term_shift(d: i32, t: Rc<Term>) -> Rc<Term> {
    fn walk(c: i32, d: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x >= c => Term::Var(*x + d).into(),
            Term::Var(_) => t,
            Term::Abs(t1) => Term::Abs(walk(c + 1, d, t1.clone())).into(),
            Term::App(t1, t2) => Term::App(walk(c, d, t1.clone()), walk(c, d, t2.clone())).into(),
        }
    }
    walk(0, d, t)
}

fn term_subst(j: i32, s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    fn walk(j: i32, s: Rc<Term>, c: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x == j + c => term_shift(c, s),
            Term::Var(_) => t,
            Term::Abs(t1) => Term::Abs(walk(j, s, c + 1, t1.clone())).into(),
            Term::App(t1, t2) => Term::App(
                walk(j, s.clone(), c, t1.clone()),
                walk(j, s.clone(), c, t2.clone()),
            )
            .into(),
        }
    }
    walk(j, s, 0, t)
}

fn term_subst_top(s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    term_shift(-1, term_subst(0, term_shift(1, s), t))
}

fn is_val(t: Rc<Term>) -> bool {
    match &*t {
        Term::Abs(_) => true,
        _ => false,
    }
}

fn eval1(t: Rc<Term>) -> Option<Rc<Term>> {
    match &*t {
        Term::App(t1, t2) => Some(match (&**t1, &**t2) {
            (Term::Abs(t12), _) if is_val(t2.clone()) => term_subst_top(t2.clone(), t12.clone()),
            _ if is_val(t1.clone()) => Term::App(t1.clone(), eval1(t2.clone())?).into(),
            _ => Term::App(eval1(t1.clone())?, t2.clone()).into(),
        }),
        _ => None,
    }
}

fn eval(t: Rc<Term>) -> Rc<Term> {
    let mut t = t;
    while let Some(next) = eval1(t.clone()) {
        t = next;
    }
    return t;
}

fn term(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, Rc<Term>> {
    move |input: &str| -> IResult<&str, Rc<Term>> {
        delimited(
            multispace0,
            alt((app_term(c.clone()), lambda(c.clone()))),
            multispace0,
        )(input)
    }
}

fn lambda(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, Rc<Term>> {
    move |input: &str| -> IResult<&str, Rc<Term>> {
        let (input, (_, _, s, _, _, _)) = tuple((
            alt((tag("lambda"), tag("λ"))),
            multispace1,
            alphanumeric1,
            multispace0,
            char('.'),
            multispace0,
        ))(input)?;

        map(term(c.with(s.into())), |t| Term::Abs(t).into())(input)
    }
}

fn atomic_term(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, Rc<Term>> {
    move |input: &str| -> IResult<&str, Rc<Term>> {
        delimited(
            multispace0,
            alt((
                delimited(char('('), term(c.clone()), char(')')),
                map_opt(alphanumeric1, |s: &str| {
                    Some(Rc::new(Term::Var(c.index(s)? as i32)))
                }),
            )),
            multispace0,
        )(input)
    }
}

fn app_term(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, Rc<Term>> {
    move |input: &str| -> IResult<&str, Rc<Term>> {
        flat_map(atomic_term(c.clone()), |t| {
            fold_many0(atomic_term(c.clone()), t, |t1, t2| Term::App(t1, t2).into())
        })(input)
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (_, t) = term(Context::new())("(λ x.x) (λ x. x x)")?;
    let result = eval(t.clone());
    println!("{:?} -> {:?}", t, result);

    let c = Context::new().with("z".into()).with("y".into());
    let (_, t) = term(c)("(λ x. y x z) (λ x. x x)")?;
    let result = eval(t.clone());
    println!("{:?} -> {:?}", t, result); // expect `0 (λ. 0) 1`

    Ok(())
}

#[test]
fn test_atomic_term() {
    let tests: Vec<(&str, Rc<Context>, Rc<Term>)> = vec![
        ("x", Context::new().with("x".into()), Term::Var(0).into()),
        (
            "λ x.x",
            Context::new(),
            Term::Abs(Term::Var(0).into()).into(),
        ),
        (
            "(λ x.x) (λ x. x x)",
            Context::new(),
            Term::App(
                Term::Abs(Term::Var(0).into()).into(),
                Term::Abs(Term::App(Term::Var(0).into(), Term::Var(0).into()).into()).into(),
            )
            .into(),
        ),
    ];

    for (input, context, expected) in tests {
        let r = term(context)(input);
        assert_eq!(r, Ok(("", expected)), "testing parse({})", input);
    }
}
