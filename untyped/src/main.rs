mod core;
mod parser;
mod syntax;

use std::rc::Rc;

use self::core::*;
use parser::*;
use syntax::*;

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
