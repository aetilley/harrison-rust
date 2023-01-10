// ### Token constants and lexing library. ###

const ALPHA: [char; 52] = [
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's',
    't', 'u', 'v', 'w', 'x', 'y', 'z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L',
    'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
];

const NUMERIC: [char; 10] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

const ALPHANUMERIC: [char; 62] = [
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's',
    't', 'u', 'v', 'w', 'x', 'y', 'z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L',
    'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', '0', '1', '2', '3', '4',
    '5', '6', '7', '8', '9',
];
const SYMBOLIC: [char; 23] = [
    '~', '`', '!', '@', '#', '$', '%', '^', '&', '*', '-', '+', '=', '|', '\\', ':', ';', '<', '>',
    '.', '?', '/', ',',
];
const PUNCTUATION: [char; 2] = ['(', ')'];

pub const INFIX_RELATION_SYMBOLS: [&str; 5] = ["<", "<=", "=", ">=", ">"];

pub fn is_const_name(name: &str) -> bool {
    // Note that we can use other constants (0-ary functions).
    // This function is intended to be used by the printer to
    // determine when to leave off the parentheses.
    // (Eg. to print "1" not "1()").
    if name == "nil" {
        return true;
    }
    for c in name.chars() {
        if !c.is_numeric() {
            return false;
        }
    }
    true
}

fn lexwhile<'a>(charset: &[char], input_chars: &'a [char]) -> usize {
    // Increment an index until the character is no longer in `charset`.
    let mut bound = 0;
    for c in input_chars {
        if charset.contains(&c) {
            bound += 1
        } else {
            break;
        }
    }
    bound
}

fn lex_inner(all_input_chars: &[char]) -> Vec<String> {
    // Build up a token list by reading one token off the
    // fron tand recursively calling itself on the remainder.

    // Drop leading whitespace.
    let space = [' '];
    let space_bound = lexwhile(&space, all_input_chars);
    let input_chars = &all_input_chars[space_bound..];
    if input_chars.len() == 0 {
        return vec![];
    }
    let head = &input_chars[0];
    let charset: &[char];
    if ALPHANUMERIC.contains(head) {
        charset = &ALPHANUMERIC
    } else if SYMBOLIC.contains(head) {
        charset = &SYMBOLIC
    } else if PUNCTUATION.contains(head) {
        charset = &[]
    } else {
        panic!("Unrecognized character {}.", head)
    }

    let bound = lexwhile(charset, &input_chars[1..]) + 1;
    let first_token = input_chars[..bound].iter().collect();
    let mut lexed_rest = lex_inner(&input_chars[bound..]);
    lexed_rest.insert(0, first_token);
    lexed_rest
}

fn explode(input: &str) -> Vec<char> {
    input.chars().collect()
}

pub fn lex(input: &str) -> Vec<String> {
    lex_inner(&explode(input)[..])
}

#[cfg(test)]
mod lex_tests {
    use super::*;
    // We use Formula for convenience in these tests, but this parent module (`parse`) should
    // not depend on `formula`.

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    // Begin Lexing tests
    #[test]
    fn lexwhile_simple() {
        let charset = vec!['a', '+', '&'];
        let input = &explode("&aw*+x")[..];
        let result = lexwhile(&charset, input);
        let desired = 2;
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex() {
        let input = "a += b";
        let result = lex(input);
        let desired = vec!["a", "+=", "b"];
        assert_eq!(result, desired);
    }

    #[test]
    fn less_simple_lex() {
        let input = "((a += b * 17) + cab)";
        let result = lex(input);
        let desired = vec!["(", "(", "a", "+=", "b", "*", "17", ")", "+", "cab", ")"];
        assert_eq!(result, desired);
    }
}
