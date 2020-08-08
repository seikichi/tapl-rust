use std::borrow::Borrow;
use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, multispace1},
    combinator::{flat_map, map, map_opt, opt},
    multi::fold_many0,
    sequence::{delimited, tuple},
    IResult,
};

#[derive(Debug, PartialEq)]
enum Term {
    Var(i32),
    Abs(String, Rc<Term>),
    App(Rc<Term>, Rc<Term>),
}

impl Term {
    fn var(n: i32) -> Rc<Term> {
        Rc::new(Term::Var(n))
    }

    fn abs(name: String, t: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Abs(name, t))
    }

    fn app(t1: Rc<Term>, t2: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::App(t1, t2))
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Binding {
    Name,
    Term(Rc<Term>),
}

#[derive(Debug, Clone, PartialEq)]
enum Command {
    Eval(Rc<Term>),
    Bind(String, Binding),
}

#[derive(Debug, PartialEq)]
enum Context {
    Cons((String, Binding), Rc<Context>),
    Nil,
}

impl Context {
    fn new() -> Rc<Self> {
        Rc::new(Context::Nil)
    }

    fn with_name(self: &Rc<Context>, x: String) -> Rc<Self> {
        self.with_binding(x, Binding::Name)
    }

    fn with_binding(self: &Rc<Context>, x: String, b: Binding) -> Rc<Self> {
        Rc::new(Context::Cons((x, b), self.clone()))
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

    fn name(self: &Rc<Context>, index: i32) -> Option<String> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons((s, b), cdr) = &*next {
            if i == index {
                return Some(s.clone());
            }
            i += 1;
            next = cdr.clone();
        }
        None
    }

    fn index<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> Option<i32> {
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

    fn is_name_bound<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> bool {
        let mut next = self.clone();
        while let Context::Cons((name, _), cdr) = &*next {
            if name == x.borrow() {
                return true;
            }
            next = cdr.clone();
        }
        false
    }

    fn pick_fresh_name<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> (Rc<Context>, String) {
        let mut name: String = x.borrow().into();
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        (self.with_name(name.clone()), name)
    }
}

fn term_shift(d: i32, t: Rc<Term>) -> Rc<Term> {
    fn walk(c: i32, d: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x >= c => Term::var(*x + d),
            Term::Var(_) => t,
            Term::Abs(n, t1) => Term::abs(n.clone(), walk(c + 1, d, t1.clone())),
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
            Term::Abs(n, t1) => Term::abs(n.clone(), walk(j, s, c + 1, t1.clone())),
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
        Term::Abs(_, _) => true,
        _ => false,
    }
}

fn eval1(t: Rc<Term>, c: Rc<Context>) -> Option<Rc<Term>> {
    match &*t {
        Term::App(t1, t2) => Some(match (&**t1, &**t2) {
            (Term::Abs(_, t12), _) if is_val(t2.clone()) => term_subst_top(t2.clone(), t12.clone()),
            _ if is_val(t1.clone()) => Term::app(t1.clone(), eval1(t2.clone(), c)?),
            _ => Term::app(eval1(t1.clone(), c)?, t2.clone()),
        }),
        Term::Var(n) => match c.get(*n)? {
            Binding::Term(t) => Some(term_shift(n + 1, t.clone())),
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

fn eval_binding(b: Binding, c: Rc<Context>) -> Binding {
    match b {
        Binding::Term(t) => Binding::Term(eval(t, c.clone())),
        _ => b,
    }
}

fn print_term(t: Rc<Term>, c: Rc<Context>) -> String {
    match &*t {
        Term::Abs(x, t1) => {
            let (c, x) = c.pick_fresh_name(x);
            format!("(λ {}. {})", x, print_term(t1.clone(), c))
        }
        Term::App(t1, t2) => format!(
            "({}. {})",
            print_term(t1.clone(), c.clone()),
            print_term(t2.clone(), c.clone())
        ),
        Term::Var(x) => c.name(*x).unwrap(),
    }
}

fn process_command(commands: &[Command]) {
    let mut context = Context::new();
    for c in commands {
        match c {
            Command::Eval(t) => {
                println!(
                    "{} -> {}",
                    print_term(t.clone(), context.clone()),
                    print_term(eval(t.clone(), context.clone()), context.clone())
                );
            }
            Command::Bind(s, b) => {
                let b = eval_binding(b.clone(), context.clone());
                match &b {
                    Binding::Name => println!("{} /", s),
                    Binding::Term(t) => {
                        println!("{} = {}", s, print_term(t.clone(), context.clone()))
                    }
                }
                context = context.with_binding(s.clone(), b);
            }
        }
    }
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

fn parse(input: &str) -> IResult<&str, Vec<Command>> {
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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (_, commands) = parse(
        "
        tru = λ t. λ f. t;
        fls = λ t. λ f. f;
        test = λ l. λ m. λ n. l m n;
        and = λ b. λ c. b c fls;

        pair = λ f. λ s. λ b. b f s;
        fst = λ p. p tru;
        snd = λ p. p fls;

        zero  = λ s. λ z. z;
        one   = λ s. λ z. s z;
        two   = λ s. λ z. s (s z);
        three = λ s. λ z. s (s (s z));
        four  = λ s. λ z. s (s (s (s z)));

        iszro = λ m. m (λ x. fls) tru;
        plus = λ m. λ n. λ s. λ z. m s (n s z);

        zz = pair zero zero;
        ss = λ p. pair (snd p) (plus one (snd p));
        prd = λ m. fst (m ss zz);

        equal = λ m. λ n. and (iszro (m prd n)) (iszro (n prd m));

        test fls zero one;

        equal (plus two two) four;
    ",
    )?;
    process_command(&commands);
    // ...
    // (((test. fls). zero). one) -> (λ s. (λ z. (s. z)))
    // ((equal. ((plus. two). two)). four) -> (λ t. (λ f. t))

    Ok(())
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

#[test]
fn test_eval() {
    let tests: Vec<(&str, Rc<Context>, Rc<Term>)> = vec![(
        "(λ x. y x z) w",
        Context::new()
            .with_binding(
                "w".into(),
                Binding::Term(Term::abs("x".into(), Term::var(0))),
            )
            .with_name("z".into())
            .with_name("y".into()),
        Term::app(
            Term::app(Term::var(0), Term::abs("x".into(), Term::var(0))),
            Term::var(1),
        ),
    )];

    for (input, context, expected) in tests {
        let (_, t) = term(context.clone())(input).unwrap();
        let r = eval(t, context);
        assert_eq!(r, expected);
    }
}
