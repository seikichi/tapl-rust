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
                println!("> {:?}\n{:?}", t, eval(t.clone(), &mut context),);
            }
            Command::Bind(s, b) => {
                println!("> {}: {:?}", s, b);
                context.add_binding(s.clone(), b.clone());
            }
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut parser = Parser::new();
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let code = fs::read_to_string(filename)?;
    let (_, commands) = parser.parse(&code).unwrap();

    process_command(&commands);

    Ok(())
}
