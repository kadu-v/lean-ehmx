use ehmx::repl::Session;
use std::io::{self, Write};

fn main() {
    let mut session = Session::new();
    println!("EHM(X) inference REPL — :help for commands");
    let stdin = io::stdin();
    loop {
        print!("ehmx> ");
        if io::stdout().flush().is_err() {
            break;
        }
        let mut line = String::new();
        match stdin.read_line(&mut line) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        match session.process(&line) {
            Ok(s) if s == "quit" => break,
            Ok(s) if !s.is_empty() => println!("{s}"),
            Ok(_) => {}
            Err(e) => eprintln!("error: {e}"),
        }
    }
}
