use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, digit1, multispace0},
    combinator::{map, map_opt},
    multi::fold_many1,
    sequence::{delimited, pair},
    IResult,
};

#[derive(Debug, PartialEq)]
enum Term {
    Var(i32),
    Abs(Rc<Term>),
    App(Rc<Term>, Rc<Term>),
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

fn parse_atomic_term(input: &str) -> IResult<&str, Rc<Term>> {
    delimited(
        multispace0,
        alt((
            delimited(char('('), parse_term, char(')')),
            map_opt(digit1, |d: &str| Some(Rc::new(Term::Var(d.parse().ok()?)))),
        )),
        multispace0,
    )(input)
}

fn parse_app_term(input: &str) -> IResult<&str, Rc<Term>> {
    fold_many1(
        parse_atomic_term,
        Term::Var(-1).into(),
        |t1: Rc<Term>, t2| {
            if let Term::Var(-1) = &*t1 {
                return t2;
            }
            Term::App(t1, t2).into()
        },
    )(input)
}

fn parse_lambda(input: &str) -> IResult<&str, Rc<Term>> {
    map(
        pair(alt((tag("lambda."), tag("λ."))), parse_term),
        |(_, t)| Term::Abs(t).into(),
    )(input)
}

fn parse_term(input: &str) -> IResult<&str, Rc<Term>> {
    delimited(
        multispace0,
        alt((parse_app_term, parse_lambda)),
        multispace0,
    )(input)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (_, term) = parse_term("(λ. 1 0 2) (λ. 0)")?;
    let result = eval(term.clone());
    println!("{:?} -> {:?}", term, result); // expect `0 (λ. 0) 1`

    Ok(())
}

#[test]
fn test_parse() {
    let tests: Vec<(&str, Rc<Term>)> = vec![
        ("0", Term::Var(0).into()),
        ("λ. 0", Term::Abs(Term::Var(0).into()).into()),
        (
            "0 1",
            Term::App(Term::Var(0).into(), Term::Var(1).into()).into(),
        ),
        (
            "0 1 2",
            Term::App(
                Term::App(Term::Var(0).into(), Term::Var(1).into()).into(),
                Term::Var(2).into(),
            )
            .into(),
        ),
        (
            "(λ. 1 0 2) (λ. 0)",
            Term::App(
                Term::Abs(
                    Term::App(
                        Term::App(Term::Var(1).into(), Term::Var(0).into()).into(),
                        Term::Var(2).into(),
                    )
                    .into(),
                )
                .into(),
                Term::Abs(Term::Var(0).into()).into(),
            )
            .into(),
        ),
    ];

    for (input, expected) in tests {
        let r = parse_term(input);
        assert_eq!(r, Ok(("", expected)), "testing parse({})", input);
    }
}
