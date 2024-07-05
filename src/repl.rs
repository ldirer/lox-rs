use std::io::{BufRead, Lines};

/// Handling multi-line input in the REPL.
/// Collecting lines until we are ready to run them. When?
/// run code on an empty line... that works, but it's a bit clunky as UI.
/// Could run on semicolon, but it's not that simple.
/// We only want to run on semicolon when we are 'balanced' (top level scope in terms of blocks at least).
/// maybe we can count characters...
/// Python seems to run the parser as input comes in.
/// >>> def f():
/// ...     a+é 1
///   File "<stdin>", line 2
///     a+é 1
///         ^
/// SyntaxError: invalid syntax
pub struct MultilineInput<T: BufRead> {
    lines: Lines<T>,
}
impl<T: BufRead> MultilineInput<T> {
    pub fn new(lines: Lines<T>) -> MultilineInput<T> {
        MultilineInput { lines }
    }
}

impl<T: BufRead> Iterator for MultilineInput<T> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let mut current_input = "".to_string();
        loop {
            let line = self.lines.next();
            if line.is_none() {
                // not sure what to do with existing current input. I guess stdin closed so it's whatever?
                // -> it changes the behavior on CTRL+D, if we return something it gets executed and the console does not exit.
                // this is what python does so doing that.
                if current_input != "".to_string() {
                    return Some(current_input);
                }
                return None;
            }
            let line = line.unwrap().expect("issue reading from stdin");
            current_input += "\n";
            current_input += &line;
            let mut open_braces: i32 = 0;
            let mut open_parens: i32 = 0;
            for char in current_input.chars() {
                match char {
                    '{' => open_braces += 1,
                    '}' => open_braces -= 1,
                    '(' => open_parens += 1,
                    ')' => open_parens -= 1,
                    _ => {}
                }
                // we could abort early if going negative, but let's rely on the parser to signal the error.
            }

            let input_finished =
                line == "" || (line.ends_with(";") && open_braces == 0 && open_parens == 0);

            if input_finished {
                return Some(current_input);
            }
        }
    }
}
