use std::rc::Rc;

use crate::syntax::*;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, multispace1},
    combinator::{flat_map, map, map_opt, opt},
    multi::fold_many0,
    sequence::{delimited, tuple},
    IResult,
};

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

        // FIXME
        let name = s.to_string();
        map(term(c.with_name(name.clone())), move |t| {
            Term::abs(name.clone(), t)
        })(input)
    }
}

fn atomic_term(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, Rc<Term>> {
    move |input: &str| -> IResult<&str, Rc<Term>> {
        delimited(
            multispace0,
            alt((
                delimited(char('('), term(c.clone()), char(')')),
                map_opt(alphanumeric1, |s: &str| {
                    Some(Rc::new(Term::Var(c.index(&s)? as i32)))
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

fn binder(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, Binding> {
    move |input: &str| -> IResult<&str, Binding> {
        alt((
            map(tuple((multispace0, char('/'))), |(_, _)| Binding::Name),
            map(
                tuple((multispace0, char('='), term(c.clone()))),
                |(_, _, t)| Binding::Term(t.clone()),
            ),
        ))(input)
    }
}

fn command(c: Rc<Context>) -> impl Fn(&str) -> IResult<&str, (Command, Rc<Context>)> {
    move |input: &str| -> IResult<&str, (Command, Rc<Context>)> {
        alt((
            map(term(c.clone()), |t| (Command::Eval(t), c.clone())),
            map(
                tuple((multispace0, alphanumeric1, binder(c.clone()))),
                |(_, s, b)| {
                    (
                        Command::Bind(s.into(), b.clone()),
                        c.with_binding(s.into(), b.clone()),
                    )
                },
            ),
        ))(input)
    }
}

pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
    let mut input = input;
    let mut context = Context::new();
    let mut commands = vec![];

    while let Ok((new_input, (command, new_context))) = command(context.clone())(input) {
        let (new_input, _) = opt(tuple((multispace0, char(';'))))(new_input)?;
        input = new_input;
        commands.push(command);
        context = new_context;
    }
    Ok((input, commands))
}

#[test]
fn test_parse() {
    let input = "x/; x; lambda x. x; (lambda x. x) (lambda x. x x)";
    let r = parse(input);
    assert_eq!(
        r,
        Ok((
            "",
            vec![
                Command::Bind("x".into(), Binding::Name),
                Command::Eval(Term::var(0)),
                Command::Eval(Term::abs("x".into(), Term::var(0))),
                Command::Eval(Term::app(
                    Term::abs("x".into(), Term::var(0)),
                    Term::abs("x".into(), Term::app(Term::var(0), Term::var(0)))
                )),
            ],
        ))
    );
}

#[test]
fn test_term() {
    let tests: Vec<(&str, Rc<Context>, Rc<Term>)> = vec![
        ("x", Context::new().with_name("x".into()), Term::var(0)),
        ("λ x.x", Context::new(), Term::abs("x".into(), Term::var(0))),
        (
            "(λ x.x) (λ x. x x)",
            Context::new(),
            Term::app(
                Term::abs("x".into(), Term::var(0)),
                Term::abs("x".into(), Term::app(Term::var(0), Term::var(0))),
            ),
        ),
    ];

    for (input, context, expected) in tests {
        let r = term(context)(input);
        assert_eq!(r, Ok(("", expected)), "testing parse({})", input);
    }
}
