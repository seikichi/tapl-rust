use crate::syntax::*;

use std::cell::RefCell;
use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric0, char, multispace0, multispace1},
    combinator::{flat_map, map, map_opt, opt, verify},
    multi::fold_many0,
    sequence::{delimited, pair, preceded, tuple},
    IResult,
};

const RESERVED_KEYWORDS: &'static [&'static str] = &["true", "false", "if", "then", "else"];

pub struct Parser {
    bindings: RefCell<Vec<String>>,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            bindings: RefCell::new(vec![]),
        }
    }

    fn get_index(&self, x: &str) -> Option<i32> {
        self.bindings
            .borrow()
            .iter()
            .rev()
            .position(|s| x == s)
            .map(|i| i as i32)
    }

    fn with_name<R, F: FnOnce() -> R>(&self, x: String, f: F) -> R {
        self.bindings.borrow_mut().push(x);
        let result = f();
        self.bindings.borrow_mut().pop();
        result
    }

    pub fn parse<'a>(&mut self, input: &'a str) -> IResult<&'a str, Vec<Command>> {
        let mut commands = vec![];
        let mut input = input;

        while let Ok((next_input, command)) = self.command(input) {
            if let Command::Bind(s, _) = &command {
                self.bindings.borrow_mut().push(s.into());
            }

            // FIXME
            let (next_input, _) = opt(tuple((multispace0, char(';'))))(next_input)?;

            input = next_input;
            commands.push(command);
        }

        Ok((input, commands))
    }

    fn command<'a>(&self, input: &'a str) -> IResult<&'a str, Command> {
        alt((
            map(|input| self.term(input), |t| Command::Eval(t)),
            map(
                pair(
                    delimited(multispace0, |input| self.identifier(input), multispace0),
                    |input| self.binder(input),
                ),
                |(s, b)| Command::Bind(s, b),
            ),
        ))(input)
    }

    fn binder<'a>(&self, input: &'a str) -> IResult<&'a str, Binding> {
        map(
            preceded(delimited(multispace0, char(':'), multispace0), |input| {
                self.all_type(input)
            }),
            |ty| Binding::Var(ty),
        )(input)
    }

    fn all_type<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Type>> {
        delimited(multispace0, |input| self.arrow_type(input), multispace0)(input)
    }

    fn atomic_type<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Type>> {
        alt((
            map(tag("Bool"), |_| Type::Bool.into()),
            delimited(
                multispace0,
                delimited(char('('), |input| self.all_type(input), char(')')),
                multispace0,
            ),
        ))(input)
    }

    fn arrow_type<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Type>> {
        flat_map(
            |input| self.atomic_type(input),
            |t| {
                fold_many0(
                    preceded(delimited(multispace0, tag("->"), multispace0), |input| {
                        self.atomic_type(input)
                    }),
                    t,
                    |t1, t2| Type::Arrow(t1, t2).into(),
                )
            },
        )(input)
    }

    fn lambda<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Term>> {
        let (input, (_, s, _, ty, _)) = tuple((
            alt((tag("lambda"), tag("λ"))),
            delimited(multispace1, |input| self.identifier(input), multispace0),
            char(':'),
            delimited(multispace0, |input| self.all_type(input), multispace0),
            char('.'),
        ))(input)?;

        self.with_name(s.clone(), || {
            map(
                |input| self.term(input),
                |t| Term::Abs(s.clone(), ty.clone(), t).into(),
            )(input)
        })
    }

    fn term<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Term>> {
        delimited(
            multispace0,
            alt((
                |input| self.if_term(input),
                |input| self.app_term(input),
                |input| self.lambda(input),
            )),
            multispace0,
        )(input)
    }

    fn if_term<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Term>> {
        map(
            tuple((
                tag("if"),
                |input| self.term(input),
                tag("then"),
                |input| self.term(input),
                tag("else"),
                |input| self.term(input),
            )),
            |(_, t1, _, t2, _, t3)| Term::If(t1, t2, t3).into(),
        )(input)
    }

    fn app_term<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Term>> {
        flat_map(
            |input| self.atomic_term(input),
            |t| {
                fold_many0(
                    |input| self.atomic_term(input),
                    t,
                    |t1, t2| Term::App(t1, t2).into(),
                )
            },
        )(input)
    }

    fn atomic_term<'a>(&self, input: &'a str) -> IResult<&'a str, Rc<Term>> {
        delimited(
            multispace0,
            alt((
                map(tag("true"), |_| Term::True.into()),
                map(tag("false"), |_| Term::False.into()),
                map_opt(
                    |input| self.identifier(input),
                    |s| Some(Term::Var(self.get_index(&s)?).into()),
                ),
                delimited(char('('), |input| self.term(input), char(')')),
            )),
            multispace0,
        )(input)
    }

    fn identifier<'a>(&self, input: &'a str) -> IResult<&'a str, String> {
        verify(
            map(pair(alpha1, alphanumeric0), |(s1, s2)| {
                format!("{}{}", s1, s2)
            }),
            |s: &String| !RESERVED_KEYWORDS.iter().any(|x| x == &s),
        )(input)
    }
}

#[test]
fn test_parser() {
    let tests: Vec<(&str, Vec<Command>)> = vec![
        (
            "λ x:Bool. x",
            vec![Command::Eval(
                Term::Abs("x".into(), Type::Bool.into(), Term::Var(0).into()).into(),
            )],
        ),
        (
            "x: Bool; λ y: Bool -> Bool. y x",
            vec![
                Command::Bind("x".into(), Binding::Var(Type::Bool.into())),
                Command::Eval(
                    Term::Abs(
                        "y".into(),
                        Type::Arrow(Type::Bool.into(), Type::Bool.into()).into(),
                        Term::App(Term::Var(0).into(), Term::Var(1).into()).into(),
                    )
                    .into(),
                ),
            ],
        ),
        (
            "(λ x: Bool -> Bool. if x false then true else false) (λ x: Bool. if x then false else true)",
            vec![Command::Eval(
                Term::App(
                    Term::Abs(
                        "x".into(),
                        Type::Arrow(Type::Bool.into(), Type::Bool.into()).into(),
                        Term::If(
                            Term::App(Term::Var(0).into(), Term::False.into()).into(),
                            Term::True.into(),
                            Term::False.into(),
                        )
                        .into(),
                    )
                    .into(),
                    Term::Abs(
                        "x".into(),
                        Type::Bool.into(),
                        Term::If(Term::Var(0).into(), Term::False.into(), Term::True.into()).into(),
                    )
                    .into(),
                )
                .into(),
            )],
        ),
    ];

    for (input, expected) in tests {
        let mut parser = Parser::new();
        let result = parser.parse(input);
        assert_eq!(result, Ok(("", expected)));
    }
}
