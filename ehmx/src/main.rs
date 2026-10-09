use ehmx::repl::Session;
use rustyline::{DefaultEditor, error::ReadlineError};

fn main() {
    let mut args = std::env::args().skip(1);
    let with_solver = match (args.next().as_deref(), args.next()) {
        (None, None) => false,
        (Some("--with-solver"), None) => true,
        _ => {
            eprintln!("usage: ehmx [--with-solver]");
            std::process::exit(2);
        }
    };
    let mut session = Session::with_solver(with_solver);
    println!(
        "EHM(X) inference REPL{} — :help for commands",
        if with_solver { " (solver)" } else { "" }
    );
    let mut editor = match DefaultEditor::new() {
        Ok(editor) => editor,
        Err(error) => {
            eprintln!("error: {error}");
            return;
        }
    };
    loop {
        let line = match editor.readline("ehmx> ") {
            Ok(line) => line,
            Err(ReadlineError::Interrupted) => continue,
            Err(ReadlineError::Eof) => break,
            Err(error) => {
                eprintln!("error: {error}");
                break;
            }
        };
        if !line.trim().is_empty() {
            if let Err(error) = editor.add_history_entry(line.as_str()) {
                eprintln!("history error: {error}");
            }
        }
        match session.process(&line) {
            Ok(s) if s == "quit" => break,
            Ok(s) if !s.is_empty() => println!("{s}"),
            Ok(_) => {}
            Err(e) => eprintln!("error: {e}"),
        }
    }
}
