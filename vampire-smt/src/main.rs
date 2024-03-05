use std::{
    env,
    ffi::OsString,
    io::{self, BufRead, Write},
    process::{Command, Stdio},
    thread,
};

use smtlib::sexp;

fn call_vampire(input: Vec<u8>, args: &[OsString]) -> Vec<u8> {
    // TODO: need to make path configurable, which means parsing command line
    let mut prog = Command::new("/Users/tchajed/sw/vampire/vampire")
        .args(["--input_syntax", "smtlib2"])
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("could not start vampire");
    let mut stdin = prog.stdin.take().unwrap();
    thread::spawn(move || {
        stdin
            .write_all(&input)
            .expect("could not write to vampire stdin");
        writeln!(stdin, "(exit)").expect("could not write to vampire stdin");
        drop(stdin);
    });
    let output = prog
        .wait_with_output()
        .expect("could not read vampire output");
    output.stdout
}

fn main() {
    let args: Vec<_> = env::args_os().skip(1).collect();
    let stdin = io::stdin();
    let mut input = Vec::new();
    let mut seen_check_sat = false;
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        input.append(&mut line.clone().into_bytes());
        if let Ok(sexp) = sexp::parse(&line) {
            if let Some((head, _args)) = sexp.app() {
                if head == "check-sat" || head == "check-sat-assuming" {
                    if seen_check_sat {
                        eprintln!("multiple check-sat commands not yet supported by wrapper");
                    }
                    let output = call_vampire(input.clone(), &args);
                    io::stdout().write_all(&output).unwrap();
                    seen_check_sat = true;
                }
                if head == "get-model" {
                    eprintln!("get-model not yet supported by wrapper");
                }
                if head == "exit" {
                    return;
                }
            }
        }
    }
}
