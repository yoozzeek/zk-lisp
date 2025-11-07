use crate::lisp::{Error, Tok};

// Lexer
pub fn lex(src: &str) -> Result<Vec<Tok>, Error> {
    let mut out = Vec::new();
    let mut it = src.chars().peekable();
    let mut i = 0usize;

    while let Some(&ch) = it.peek() {
        match ch {
            '(' => {
                out.push(Tok::LParen);
                it.next();

                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                it.next();

                i += 1;
            }
            ' ' | '\n' | '\r' | '\t' => {
                it.next();
                i += 1;
            }
            '0'..='9' => {
                let mut s = String::new();
                while let Some(&c2) = it.peek() {
                    if c2.is_ascii_digit() {
                        s.push(c2);
                        it.next();

                        i += 1;
                    } else {
                        break;
                    }
                }

                let v = s.parse::<u64>().unwrap();
                out.push(Tok::Int(v));
            }
            _ => {
                if is_sym_start(ch) {
                    let mut s = String::new();
                    while let Some(&c2) = it.peek() {
                        if is_sym_continue(c2) {
                            s.push(c2);
                            it.next();

                            i += 1;
                        } else {
                            break;
                        }
                    }

                    out.push(Tok::Sym(s));
                } else {
                    return Err(Error::Lex(ch, i));
                }
            }
        }
    }

    out.push(Tok::Eof);

    Ok(out)
}

fn is_sym_start(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '+' | '-' | '*' | '=' | '<' | '>' )
}

fn is_sym_continue(c: char) -> bool {
    is_sym_start(c) || matches!(c, '0'..='9' | '/' | ':')
}
