// A minimal algebraic ast, parser, printer, and simplifier
// intended mostly for educational purposes.
//
use crate::parse::generic_parser;

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Const(i32),
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}
pub use Expression as Expr;

pub fn constant(val: i32) -> Expr {
    Expr::Const(val)
}

pub fn var(val: &str) -> Expr {
    Expr::Var(String::from(val))
}

pub fn add(expr1: Expr, expr2: Expr) -> Expr {
    // TAKES OWNERSHIP
    Expr::Add(Box::new(expr1), Box::new(expr2))
}

pub fn mul(expr1: Expr, expr2: Expr) -> Expr {
    // TAKES OWNERSHIP
    Expr::Mul(Box::new(expr1), Box::new(expr2))
}

fn parse_expression(expr: &[String]) -> (Expr, &[String]) {
    match parse_product(expr) {
        (expr1, [x, i1 @ ..]) if x == "+" => {
            let (expr2, i2) = parse_expression(i1);
            (add(expr1, expr2), i2)
        }
        (expr1, [i1 @ ..]) => (expr1, i1),
    }
}

fn parse_product(expr: &[String]) -> (Expr, &[String]) {
    match parse_atom(expr) {
        (expr1, [x, i1 @ ..]) if x == "*" => {
            let (expr2, i2) = parse_product(i1);
            (mul(expr1, expr2), i2)
        }
        (expr1, [i1 @ ..]) => (expr1, i1),
    }
}

fn parse_atom(expr: &[String]) -> (Expr, &[String]) {
    match expr {
        [] => {
            panic!("Expected an expression at end of input.");
        }
        [token, i1 @ ..] if token == "(" => match parse_expression(i1) {
            (expr1, [x, i2 @ ..]) if x == ")" => (expr1, i2),
            _ => {
                panic!("Expected closing bracket");
            }
        },
        [token, i1 @ ..] => match token.parse::<i32>() {
            Ok(value) => (constant(value), i1),
            Err(_) => (var(token), i1),
        },
    }
}

fn toy_parser(input: &str) -> Expr {
    generic_parser(parse_expression, input)
}

fn expr_to_str(priority: i32, expr: &Expr) -> String {
    match expr {
        Expr::Var(x) => x.clone(),
        Expr::Const(n) => n.to_string(),
        Expr::Add(box expr1, box expr2) => {
            let s = format!("{} + {}", expr_to_str(3, expr1), expr_to_str(2, expr2));
            if priority > 2 {
                format!("({})", s)
            } else {
                format!("{}", s)
            }
        }
        Expr::Mul(box expr1, box expr2) => {
            let s = format!("{} * {}", expr_to_str(5, expr1), expr_to_str(4, expr2));
            if priority > 4 {
                format!("({})", s)
            } else {
                format!("{}", s)
            }
        }
    }
}

fn pretty_print(expr: &Expr) -> String {
    format!("<<{}>>", expr_to_str(0, expr))
}

#[cfg(test)]
mod toy_parse_tests {
    use super::*;
    #[test]
    fn parse_atom_0() {
        let input_strs = ["ab"];
        let input: Vec<String> = input_strs.iter().map(|x| x.to_string()).collect();
        let result = parse_expression(&input[..]);
        let empty: &[String] = &[];
        let desired = (var("ab"), empty);
        assert_eq!(result, desired);
    }

    #[test]
    fn parse_1() {
        let input_strs = ["(", "(", "ab", "+", "c", "*", "17", ")", "+", "c1b", ")"];
        let input: Vec<String> = input_strs.iter().map(|x| x.to_string()).collect();
        let result = parse_expression(&input[..]);
        let empty: &[String] = &[];
        let desired = (
            add(add(var("ab"), mul(var("c"), constant(17))), var("c1b")),
            empty,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn default_parser_1_simple() {
        let input = "((ab + c * 17) + c1b)";
        let result = toy_parser(input);
        let desired = add(add(var("ab"), mul(var("c"), constant(17))), var("c1b"));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_pretty_print_simple() {
        let input = add(add(var("ab"), mul(var("c"), constant(17))), var("c1b"));
        let result = pretty_print(&input);
        let desired = "<<(ab + c * 17) + c1b>>";
        assert_eq!(result, desired);
    }
}

// SIMPLIFICATION

// NOTE THE FOLLOWING does not require nightly but has a significantly more
// cumbersome way of destructuring box expressions. We include it to give a hint
// at what would be required, but in most of this project we avail
// ourselves of [feature(box_patters)].
//
// Note that Box::new(T) constructs a Box<T>(Unique<T>).
// Thus to recover the T a double dereference (**) is required.

// fn simplify1(expr: &Expr) -> Expr {
//     // Note:  One can match directly on box patterns in unstable rust:
//     // https://doc.rust-lang.org/beta/unstable-book/language-features/box-patterns.html
//     match expr {
//         Expr::Add(x, y) => match (&**x, &**y) {
//             (Expr::Const(n), Expr::Const(m)) => Expr::Const(n + m),
//             (Expr::Const(0), ref ex) | (ref ex, Expr::Const(0)) => (*ex).clone(),
//             _ => expr.clone(),
//         },
//
//         Expr::Mul(x, y) => match (&**x, &**y) {
//             (Expr::Const(n), Expr::Const(m)) => Expr::Const(n * m),
//             (Expr::Const(0), _) | (_, Expr::Const(0)) => Expr::Const(0),
//             (Expr::Const(1), ref ex) | (ref ex, Expr::Const(1)) => (*ex).clone(),
//             _ => expr.clone(),
//         },
//
//         _ => expr.clone(),
//     }
// }

// REQUIRES NIGHTLY
fn simplify1(expr: &Expr) -> Expr {
    match expr {
        Expr::Add(box Expr::Const(n), box Expr::Const(m)) => Expr::Const(n + m),
        Expr::Add(box Expr::Const(0), box ex) => ex.clone(),
        Expr::Add(box ex, box Expr::Const(0)) => ex.clone(),

        Expr::Mul(box Expr::Const(n), box Expr::Const(m)) => Expr::Const(n * m),
        Expr::Mul(box Expr::Const(0), box _ex) => Expr::Const(0),
        Expr::Mul(box _ex, box Expr::Const(0)) => Expr::Const(0),
        Expr::Mul(box Expr::Const(1), box ex) => ex.clone(),
        Expr::Mul(box ex, box Expr::Const(1)) => ex.clone(),

        _ => expr.clone(),
    }
}

fn simplify(expr: &Expr) -> Expr {
    match expr {
        Expr::Add(box x, box y) => simplify1(&add(simplify(x), simplify(y))),
        Expr::Mul(box x, box y) => simplify1(&mul(simplify(x), simplify(y))),
        _ => expr.clone(),
    }
}

#[cfg(test)]
mod simplification_tests {
    use super::*;
    #[test]
    fn expr_eq() {
        let b = add(constant(42), var("hello"));
        let c = add(constant(42), var("hello"));
        assert_eq!(b, c);
    }

    #[test]
    fn simplify1_add_consts() {
        let b = add(Expr::Const(42), Expr::Const(43));
        let result = simplify1(&b);
        let desired = Expr::Const(42 + 43);
        assert_eq!(result, desired);
    }

    #[test]
    fn simplify1_add_zero() {
        let b = add(constant(42), constant(43));
        let c1 = add(b.clone(), constant(0));
        let c2 = add(constant(0), b.clone());
        let result1 = simplify1(&c1);
        let result2 = simplify1(&c2);
        assert_eq!(result1, b);
        assert_eq!(result2, b);
    }

    #[test]
    fn simplify1_mul_consts() {
        let b = mul(constant(42), constant(43));
        let result = simplify1(&b);
        let desired = Expr::Const(42 * 43);
        assert_eq!(result, desired);
    }

    #[test]
    fn simplify1_mul_zero() {
        let b = add(constant(42), constant(43));
        let c1 = mul(b.clone(), constant(0));
        let c2 = mul(constant(0), b.clone());
        let result1 = simplify1(&c1);
        let result2 = simplify1(&c2);
        assert_eq!(result1, constant(0));
        assert_eq!(result2, constant(0));
    }

    #[test]
    fn simplify1_mul_one() {
        let b = add(constant(42), constant(43));
        let c1 = mul(b.clone(), constant(1));
        let c2 = mul(constant(1), b.clone());
        let result1 = simplify1(&c1);
        let result2 = simplify1(&c2);
        assert_eq!(result1, b);
        assert_eq!(result2, b);
    }

    #[test]
    fn simplify_basic() {
        // (0 * x + 1) * 3 + 12 = 15
        let b = add(
            mul(add(mul(constant(0), var("x")), constant(1)), constant(3)),
            constant(12),
        );
        let result = simplify(&b);
        let desired = constant(15);
        assert_eq!(result, desired);
    }
}
