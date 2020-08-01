extern crate nom;

use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace0},
    combinator::map,
    sequence::{delimited, pair, tuple},
    IResult,
};

#[derive(Debug, PartialEq)]
enum Term {
    True,
    False,
    If(Rc<Term>, Rc<Term>, Rc<Term>),
    Zero,
    Succ(Rc<Term>),
    Pred(Rc<Term>),
    IsZero(Rc<Term>),
}

fn is_numeric_val(t: Rc<Term>) -> bool {
    match &*t {
        Term::Zero => true,
        Term::Succ(t1) => is_numeric_val(t1.clone()),
        _ => false,
    }
}

// fn is_val(t: Rc<Term>) -> bool {
//     match &*t {
//         Term::True => true,
//         Term::False => true,
//         _ if is_numeric_val(t.clone()) => true,
//         _ => false,
//     }
// }

fn eval1(t: Rc<Term>) -> Option<Rc<Term>> {
    match &*t {
        Term::If(t1, t2, t3) => Some(match &**t1 {
            Term::True => t2.clone(),
            Term::False => t3.clone(),
            _ => Term::If(eval1(t1.clone())?, t2.clone(), t3.clone()).into(),
        }),
        Term::Succ(t1) => Some(Term::Succ(eval1(t1.clone())?).into()),
        Term::Pred(t1) => Some(match &**t1 {
            Term::Succ(nv1) if is_numeric_val(nv1.clone()) => nv1.clone(),
            _ => Term::Pred(eval1(t1.clone())?).into(),
        }),
        Term::IsZero(t1) => Some(match &**t1 {
            Term::Zero => Term::True.into(),
            Term::Succ(nv1) if is_numeric_val(nv1.clone()) => Term::False.into(),
            _ => Term::IsZero(eval1(t1.clone())?).into(),
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

fn parse_constant(input: &str) -> IResult<&str, Rc<Term>> {
    alt((
        map(tag("0"), |_| Term::Zero.into()),
        map(tag("true"), |_| Term::True.into()),
        map(tag("false"), |_| Term::False.into()),
    ))(input)
}

fn parse_function(input: &str) -> IResult<&str, Rc<Term>> {
    alt((
        map(pair(tag("succ"), parse_term), |(_, t)| Term::Succ(t).into()),
        map(pair(tag("pred"), parse_term), |(_, t)| Term::Pred(t).into()),
        map(pair(tag("iszero"), parse_term), |(_, t)| {
            Term::IsZero(t).into()
        }),
    ))(input)
}

fn parse_if(input: &str) -> IResult<&str, Rc<Term>> {
    map(
        tuple((
            tag("if"),
            parse_term,
            tag("then"),
            parse_term,
            tag("else"),
            parse_term,
        )),
        |(_, t1, _, t2, _, t3)| Term::If(t1, t2, t3).into(),
    )(input)
}

fn parse_term(input: &str) -> IResult<&str, Rc<Term>> {
    delimited(
        multispace0,
        alt((
            parse_constant,
            parse_if,
            parse_function,
            delimited(char('('), parse_term, char(')')),
        )),
        multispace0,
    )(input)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (_, term) = parse_term("iszero (pred (succ (succ 0)))")?;
    println!("eval({:?}) -> {:?}", term, eval(term.clone()));

    let (_, term) = parse_term("if false then true else false")?;
    println!("eval({:?}) -> {:?}", term, eval(term.clone()));

    Ok(())
}

#[test]
fn test_parse() {
    let tests: Vec<(&str, Rc<Term>)> = vec![
        ("0", Term::Zero.into()),
        ("succ 0", Term::Succ(Term::Zero.into()).into()),
        (
            "iszero (pred (succ 0))",
            Term::IsZero(Term::Pred(Term::Succ(Term::Zero.into()).into()).into()).into(),
        ),
        (
            "if false then true else false",
            Term::If(Term::False.into(), Term::True.into(), Term::False.into()).into(),
        ),
        (
            "if iszero (pred (succ 0)) then (if false then false else false) else false",
            Term::If(
                Term::IsZero(Term::Pred(Term::Succ(Term::Zero.into()).into()).into()).into(),
                Term::If(Term::False.into(), Term::False.into(), Term::False.into()).into(),
                Term::False.into(),
            )
            .into(),
        ),
    ];

    for (input, expected) in tests {
        let r = parse_term(input);
        assert_eq!(r, Ok(("", expected)), "testing parse({})", input);
    }
}

#[test]
fn test_eval() {
    let tests: Vec<(&str, Rc<Term>)> = vec![
        ("0", Term::Zero.into()),
        ("succ 0", Term::Succ(Term::Zero.into()).into()),
        ("iszero (pred (succ 0))", Term::True.into()),
    ];

    for (input, expected) in tests {
        let (_, term) = parse_term(input).unwrap();
        assert_eq!(eval(term), expected, "testing eval(parse({}))", input);
    }
}
