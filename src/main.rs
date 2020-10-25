#![allow(dead_code)]

mod ast;
mod buffer;
mod compile;
mod emit;
mod env;
mod exec;
mod object;
mod reader;

use std::io::{stdin, stdout, BufRead, Write};

fn main() {
    if std::env::args().nth(1) == Some("--repl-assembly".to_string()) {
        repl().expect("Fatal error");
    }
}

fn repl() -> Result<(), std::io::Error> {
    macro_rules! compiler {
        () => {{
            compile::Compiler::new(emit::Emit::new(
                buffer::Buffer::new(10).expect("Failed to allocate buffer"),
            ))
        }};
    }

    print!("lisp> ");
    stdout().flush()?;
    for line in stdin().lock().lines() {
        let node = reader::read(line?.as_ref())
            .map_err(|e| println!("Parse error: {}", e))
            .ok();

        if let Some(node) = node {
            let mut cmp = compiler!();
            if let Err(e) =
                cmp.compile_expr(&node, -(object::WORD_SIZE as isize), &mut env::Env::new())
            {
                println!("Compile error: {}", e);
            } else {
                println!(
                    "{}",
                    cmp.finish()
                        .code()
                        .iter()
                        .map(|i| format!("{:02x}", i))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let mut cmp = compiler!();
                if let Err(e) = cmp.compile_function(&node, &mut env::Env::new()) {
                    println!("Compile error: {}", e);
                } else {
                    match &mut cmp.finish().make_executable() {
                        // FIXME: always prints result as a number
                        Ok(exec) => println!("Result: {}", object::decode_integer(exec.exec())),
                        Err(e) => println!("Failed to make executable: {}", e),
                    }
                }
            }
        }

        print!("\nlisp> ");
        stdout().flush()?;
    }

    Ok(())
}
