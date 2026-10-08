use ehmx::repl::Session;
use rustyline::{DefaultEditor, error::ReadlineError};

fn main() {
    let mut session = Session::new();
    println!("EHM(X) inference REPL — :help for commands");
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
