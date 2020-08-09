mod core;
mod parser;
mod syntax;

use std::env;
use std::fs;

use self::core::*;
use parser::*;
use syntax::*;

fn process_command(commands: &[Command]) {
    let mut context = Context::new();
    for c in commands {
        match c {
            Command::Eval(t) => {
                println!(
                    "> {}\n{}",
                    t.display(context.clone()),
                    eval(t.clone(), context.clone()).display(context.clone()),
                );
            }
            Command::Bind(s, b) => {
                let b = eval_binding(b.clone(), context.clone());
                println!("> {}{}", s, b.display(context.clone()));
                context = context.with_binding(s.clone(), b);
            }
        }
    }
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let code = fs::read_to_string(filename)?;
    let (_, commands) = parse(&code).unwrap();

    process_command(&commands);

    Ok(())
}
