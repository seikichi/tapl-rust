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

impl Term {
    fn var(n: i32) -> Rc<Term> {
        Rc::new(Term::Var(n))
    }

    fn abs(t: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Abs(t))
    }

    fn app(t1: Rc<Term>, t2: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::App(t1, t2))
    }
}

#[derive(Debug, Clone)]
enum Binding {
    Name,
    Term(Rc<Term>),
}

#[derive(Debug)]
enum Context {
    Cons((String, Binding), Rc<Context>),
    Nil,
}

impl Context {
    fn new() -> Rc<Self> {
        Rc::new(Context::Nil)
    }

    fn with_name(self: &Rc<Context>, x: String) -> Rc<Self> {
        Rc::new(Context::Cons((x, Binding::Name), self.clone()))
    }

    fn with_binding(self: &Rc<Context>, x: String, t: Rc<Term>) -> Rc<Self> {
        Rc::new(Context::Cons((x, Binding::Term(t)), self.clone()))
    }

    fn get(self: &Rc<Context>, index: i32) -> Option<Binding> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons((_, b), cdr) = &*next {
            if i == index {
                return Some(b.clone());
            }
            i += 1;
            next = cdr.clone();
        }
        None
    }

    fn index<T: Borrow<str>>(self: &Rc<Context>, x: T) -> Option<i32> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons((name, _), cdr) = &*next {
            if name == x.borrow() {
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
            Term::Var(x) if *x >= c => Term::var(*x + d),
            Term::Var(_) => t,
            Term::Abs(t1) => Term::abs(walk(c + 1, d, t1.clone())),
            Term::App(t1, t2) => Term::app(walk(c, d, t1.clone()), walk(c, d, t2.clone())),
        }
    }
    walk(0, d, t)
}

fn term_subst(j: i32, s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    fn walk(j: i32, s: Rc<Term>, c: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x == j + c => term_shift(c, s),
            Term::Var(_) => t,
            Term::Abs(t1) => Term::abs(walk(j, s, c + 1, t1.clone())),
            Term::App(t1, t2) => Term::app(
                walk(j, s.clone(), c, t1.clone()),
                walk(j, s.clone(), c, t2.clone()),
            ),
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

fn eval1(t: Rc<Term>, c: Rc<Context>) -> Option<Rc<Term>> {
    match &*t {
        Term::App(t1, t2) => Some(match (&**t1, &**t2) {
            (Term::Abs(t12), _) if is_val(t2.clone()) => term_subst_top(t2.clone(), t12.clone()),
            _ if is_val(t1.clone()) => Term::app(t1.clone(), eval1(t2.clone(), c)?),
            _ => Term::app(eval1(t1.clone(), c)?, t2.clone()),
        }),
        Term::Var(n) => match c.get(*n)? {
            Binding::Term(t) => Some(t.clone()), // Some(term_shift(n + 1, t.clone())),
            Binding::Name => None,
        },
        _ => None,
    }
}

fn eval(t: Rc<Term>, c: Rc<Context>) -> Rc<Term> {
    let mut t = t;
    while let Some(next) = eval1(t.clone(), c.clone()) {
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

        map(term(c.with_name(s.into())), |t| Term::abs(t))(input)
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
    let result = eval(t.clone(), Context::new());
    println!("{:?} -> {:?}", t, result);

    let c = Context::new().with_name("z".into()).with_name("y".into());
    let (_, t) = term(c)("(λ x. y x z) (λ x. x)")?;
    let result = eval(t.clone(), Context::new());
    println!("{:?} -> {:?}", t, result); // expect `0 (λ. 0) 1`

    Ok(())
}

#[test]
fn test_term() {
    let tests: Vec<(&str, Rc<Context>, Rc<Term>)> = vec![
        ("x", Context::new().with_name("x".into()), Term::var(0)),
        ("λ x.x", Context::new(), Term::abs(Term::var(0))),
        (
            "(λ x.x) (λ x. x x)",
            Context::new(),
            Term::app(
                Term::abs(Term::var(0)),
                Term::abs(Term::app(Term::var(0), Term::var(0))),
            ),
        ),
    ];

    for (input, context, expected) in tests {
        let r = term(context)(input);
        assert_eq!(r, Ok(("", expected)), "testing parse({})", input);
    }
}

#[test]
fn test_eval() {
    let tests: Vec<(&str, Rc<Context>, Rc<Term>)> = vec![(
        "(λ x. y x z) w",
        Context::new()
            .with_binding("w".into(), Term::abs(Term::var(0)))
            .with_name("z".into())
            .with_name("y".into()),
        Term::app(
            Term::app(Term::var(0), Term::abs(Term::var(0))),
            Term::var(1),
        ),
    )];

    for (input, context, expected) in tests {
        let (_, t) = term(context.clone())(input).unwrap();
        let r = eval(t, context);
        assert_eq!(r, expected);
    }
}
