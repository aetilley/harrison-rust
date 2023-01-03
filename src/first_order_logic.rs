// ### First Order Logic ###
// AST specific parsing/printing functions for first-order (aka predicate) logic.
//
use std::io::Write;

use crate::formula::{close_box, open_box, parse_formula, print_break, write, ErrInner, Formula};
use crate::parse::{
    generic_parser, parse_bracketed, parse_bracketed_list, parse_left_infix, parse_list,
    parse_right_infix, ListSubparser, PartialParseResult, Subparser, SubparserFuncListType,
    SubparserFuncType,
};
use crate::token::{is_const_name, INFIX_RELATION_SYMBOLS};

// ### Term ###
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

impl Term {
    // Convenience builders for Terms.
    fn var(name: &str) -> Term {
        Term::Var(String::from(name))
    }

    fn fun(name: &str, terms: &[Term]) -> Term {
        Term::Fun(String::from(name), terms.to_owned())
    }

    fn constant(name: &str) -> Term {
        Term::fun(name, &[])
    }

    pub fn add(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("+"), vec![t1, t2])
    }
    pub fn unary_minus(t: Term) -> Term {
        Term::Fun(String::from("-"), vec![t])
    }
    pub fn sub(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("-"), vec![t1, t2])
    }
    pub fn mul(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("*"), vec![t1, t2])
    }
    pub fn div(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("/"), vec![t1, t2])
    }
    pub fn exp(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("^"), vec![t1, t2])
    }
    // The inclusion of infix list constructor is a bit
    // surprising and seems to imply that domains will often
    // be closed under cartesian products.
    pub fn cons(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("::"), vec![t1, t2])
    }
}

#[cfg(test)]
mod term_basic_tests {

    use super::*;

    #[test]
    fn test_term_eq() {
        let t1 = Term::var("a");
        let t2 = Term::var("b");
        let t3 = Term::var("b");
        let t4 = Term::fun("c", &[Term::var("f"), Term::fun("a", &[Term::var("d")])]);
        let t5 = Term::fun("c", &[Term::var("f"), Term::fun("a", &[Term::var("d")])]);
        let t6 = Term::fun("c", &[Term::var("f"), Term::fun("a", &[Term::var("e")])]);

        assert_ne!(t1, t2);
        assert_eq!(t2, t3);
        assert_eq!(t4, t5);
        assert_ne!(t5, t6);
    }
}

// ### TERM PARSING ###
impl Term {
    fn parse_atomic_term<'a>(
        variables: &Vec<String>,
        input: &'a [String],
    ) -> PartialParseResult<'a, Term> {
        let minus = "-";
        match input {
            [] => panic!("Term expected."),
            [head, rest @ ..] if head == "(" => parse_bracketed(
                Subparser {
                    fun: &|input| Term::parse_term(variables, input),
                },
                rest,
            ),
            [f, rest @ ..] if f == minus => {
                let (term, newrest) = Term::parse_atomic_term(variables, rest);
                (Term::Fun(String::from(minus), vec![term]), newrest)
            }
            [f, x, rest @ ..] if x == "(" => {
                let term_subparser: SubparserFuncType<Term> =
                    &|input| Term::parse_term(variables, input);
                let list_subparser: SubparserFuncListType<Term> = &|input| {
                    parse_list(
                        ",",
                        Subparser {
                            fun: term_subparser,
                        },
                        input,
                    )
                };
                let (terms, newrest) = parse_bracketed_list(
                    ListSubparser {
                        fun: list_subparser,
                    },
                    rest,
                );
                (Term::Fun(f.clone(), terms), newrest)
            }
            [a, rest @ ..] => {
                if is_const_name(a) && !variables.contains(a) {
                    (Term::Fun(a.clone(), vec![]), rest)
                } else {
                    (Term::Var(a.clone()), rest)
                }
            }
        }
    }

    fn parse_term<'a>(
        variables: &Vec<String>,
        input: &'a [String],
    ) -> PartialParseResult<'a, Term> {
        let atomic_subparser: SubparserFuncType<Term> =
            &|input| Term::parse_atomic_term(variables, input);
        let exp_subparser: SubparserFuncType<Term> = &|input| {
            parse_left_infix(
                "^",
                Term::exp,
                Subparser {
                    fun: atomic_subparser,
                },
                input,
            )
        };
        let div_subparser: SubparserFuncType<Term> =
            &|input| parse_left_infix("/", Term::div, Subparser { fun: exp_subparser }, input);
        let mul_subparser: SubparserFuncType<Term> =
            &|input| parse_right_infix("*", Term::mul, Subparser { fun: div_subparser }, input);
        let sub_subparser: SubparserFuncType<Term> =
            &|input| parse_left_infix("-", Term::sub, Subparser { fun: mul_subparser }, input);
        let add_subparser: SubparserFuncType<Term> =
            &|input| parse_right_infix("+", Term::add, Subparser { fun: sub_subparser }, input);
        let cons_subparser: SubparserFuncType<Term> =
            &|input| parse_right_infix("::", Term::cons, Subparser { fun: add_subparser }, input);
        let parser = cons_subparser;
        parser(input)
    }

    fn parse_term_inner<'a>(input: &'a [String]) -> PartialParseResult<'a, Term> {
        Term::parse_term(&vec![], input)
    }

    fn parset(input: &str) -> Term {
        generic_parser(Term::parse_term_inner, input)
    }
}

#[cfg(test)]
mod term_parse_tests {

    use super::*;
    use crate::utils::to_vec_of_owned;

    #[test]
    fn test_parse_term_simple_1() {
        let input_vec: Vec<String> = to_vec_of_owned(vec!["(", "13", "+", "x", ")", "/", "A"]);

        let input: &[String] = &input_vec[..];

        let result: PartialParseResult<Term> = Term::parse_term(&vec![], input);

        let desired_rest: &[String] = &[];
        let desired = (
            Term::div(
                Term::add(Term::constant("13"), Term::var("x")),
                Term::var("A"),
            ),
            desired_rest,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_term_simple_2() {
        let input_vec: Vec<String> =
            to_vec_of_owned(vec!["apples", "*", "-", "oranges", "-", "42"]);

        let input: &[String] = &input_vec[..];

        let result: PartialParseResult<Term> = Term::parse_term(&vec![], input);

        let desired_rest: &[String] = &[];
        let desired = (
            Term::sub(
                Term::mul(Term::var("apples"), Term::unary_minus(Term::var("oranges"))),
                Term::constant("42"),
            ),
            desired_rest,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_term_simple_3() {
        let input_vec: Vec<String> = to_vec_of_owned(vec![
            "F", "(", "V", ",", "apples", "::", "oranges", "::", "42", ",", "19", ")",
        ]);

        let input: &[String] = &input_vec[..];

        let result: PartialParseResult<Term> = Term::parse_term(&vec![], input);

        let desired_rest: &[String] = &[];
        let desired = (
            Term::fun(
                "F",
                &[
                    Term::var("V"),
                    Term::fun(
                        "::",
                        &[
                            Term::var("apples"),
                            Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                        ],
                    ),
                    Term::constant("19"),
                ],
            ),
            desired_rest,
        );
        assert_eq!(result, desired);
    }
}

// ### TERM PRINTING ###
impl Term {
    fn print_term<W: Write>(dest: &mut W, prec: u32, term: &Term) {
        match term {
            Term::Var(x) => {
                write(dest, &x);
            }
            Term::Fun(op, args) if op == "^" && args.len() == 2 => {
                Term::print_infix_term(dest, true, prec, 24, "^", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "/" && args.len() == 2 => {
                Term::print_infix_term(dest, true, prec, 22, " / ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "*" && args.len() == 2 => {
                Term::print_infix_term(dest, false, prec, 20, " * ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "-" && args.len() == 2 => {
                Term::print_infix_term(dest, true, prec, 18, " - ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "+" && args.len() == 2 => {
                Term::print_infix_term(dest, false, prec, 16, " + ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "::" && args.len() == 2 => {
                Term::print_infix_term(dest, false, prec, 14, "::", &args[0], &args[1])
            }
            Term::Fun(f, args) => Term::print_fargs(dest, &f, &args),
        }
    }

    fn print_fargs<W: Write>(dest: &mut W, f: &str, args: &Vec<Term>) {
        // Print a prefix predicate/function application e.g. R(x, y, ...), or f(u, v, ...)
        write(dest, f);
        match &args[..] {
            [] => {
                return;
            } // Dont' print parens for constants and propositions
            [head, rest @ ..] => {
                write(dest, "(");
                open_box(0);
                Term::print_term(dest, 0, &head);
                for term in rest {
                    write(dest, ",");
                    print_break(dest, 0, 0);
                    Term::print_term(dest, 0, &term);
                }
                close_box();
                write(dest, ")");
            }
        }
    }

    fn print_infix_term<W: Write>(
        dest: &mut W,
        is_left: bool,
        old_prec: u32,
        new_prec: u32,
        symbol: &str,
        term1: &Term,
        term2: &Term,
    ) {
        if old_prec > new_prec {
            write(dest, "(");
            open_box(0);
        }
        Term::print_term(dest, if is_left { new_prec } else { new_prec + 1 }, &term1);
        // print_break(0,0)
        write(dest, symbol);
        // print_break(
        //     dest,
        //     if symbol.chars().nth(0).unwrap() == ' ' {
        //         1
        //     } else {
        //         0
        //     },
        //     0,
        // );
        Term::print_term(dest, if is_left { new_prec + 1 } else { new_prec }, &term2);
        if old_prec > new_prec {
            write(dest, ")");
            open_box(0);
        }
    }

    fn pprint<W: Write>(&self, dest: &mut W) -> () {
        open_box(0);
        write(dest, "<<|");
        open_box(0);
        Term::print_term(dest, 0, self);
        close_box();
        write(dest, "|>>");
        close_box();
    }
}

#[cfg(test)]
mod term_print_tests {

    use super::*;

    #[test]
    fn test_print_term_simple_1() {
        let term = Term::div(
            Term::add(Term::constant("13"), Term::var("x")),
            Term::var("A"),
        );

        let mut output = Vec::new();

        term.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");

        let desired = "<<|(13 + x) / A|>>";

        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_term_simple_2() {
        let term = Term::sub(
            Term::mul(Term::var("apples"), Term::unary_minus(Term::var("oranges"))),
            Term::constant("42"),
        );
        let mut output = Vec::new();

        term.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<|apples * -(oranges) - 42|>>";
        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_term_simple_3() {
        let term = Term::fun(
            "F",
            &[
                Term::var("V"),
                Term::fun(
                    "::",
                    &[
                        Term::var("apples"),
                        Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                    ],
                ),
                Term::constant("19"),
            ],
        );
        let mut output = Vec::new();

        term.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<|F(V, apples::oranges::42, 19)|>>";
        assert_eq!(output, desired);
    }
}

// A Relation / n-ary Predicate
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct Pred {
    name: String,
    terms: Vec<Term>,
}

impl Pred {
    pub fn pred(name: &str, terms: &[Term]) -> Pred {
        // Convenience constructor for `Pred`s.
        Pred {
            name: String::from(name),
            terms: terms.to_owned(),
        }
    }

    fn print_pred<W: Write>(dest: &mut W, _prec: u32, Pred { name, terms }: &Pred) {
        if INFIX_RELATION_SYMBOLS.contains(&name.as_str()) && terms.len() == 2 {
            Term::print_infix_term(
                dest,
                false,
                12,
                12,
                &format!(" {} ", name),
                &terms[0],
                &terms[1],
            );
        } else {
            Term::print_fargs(dest, &name, terms);
        }
    }
}

#[cfg(test)]
mod pred_print_tests {

    use super::*;

    #[test]
    fn print_pred_test_prefix() {
        let pred = Pred::pred(
            "R",
            &[
                Term::var("V"),
                Term::fun(
                    "::",
                    &[
                        Term::var("apples"),
                        Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                    ],
                ),
                Term::constant("19"),
            ],
        );
        let mut output = Vec::new();
        Pred::print_pred(&mut output, 0, &pred);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "R(V, apples::oranges::42, 19)";
        assert_eq!(output, desired);
    }

    #[test]
    fn print_pred_test_infix() {
        let pred = Pred::pred(
            "<=",
            &[
                Term::fun(
                    "::",
                    &[
                        Term::var("apples"),
                        Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                    ],
                ),
                Term::constant("19"),
            ],
        );
        let mut output = Vec::new();
        Pred::print_pred(&mut output, 0, &pred);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "apples::oranges::42 <= 19";
        assert_eq!(output, desired);
    }
}

// ### A first-order (predicate) logic formula. ###
//
// ### PARSING ###
impl Formula<Pred> {
    fn _infix_parser<'a>(
        variables: &Vec<String>,
        input: &'a [String],
    ) -> Result<PartialParseResult<'a, Formula<Pred>>, ErrInner> {
        let (term1, rest) = Term::parse_term(variables, input);
        if rest.len() == 0 || !INFIX_RELATION_SYMBOLS.contains(&rest[0].as_str()) {
            return Err("Not infix.");
        }
        let (term2, newrest) = Term::parse_term(variables, &rest[1..]);
        Ok((
            Formula::atom(Pred::pred(&rest[0], &[term1, term2])),
            newrest,
        ))
    }

    fn _atom_parser<'a>(
        variables: &Vec<String>,
        input: &'a [String],
    ) -> PartialParseResult<'a, Formula<Pred>> {
        if let Ok(parse_result) = Formula::_infix_parser(variables, input) {
            return parse_result;
        };
        // Else not infix atom.
        match input {
            [p, x, rest @ ..] if x == "(" => {
                let term_subparser: SubparserFuncType<Term> =
                    &|input| Term::parse_term(variables, input);
                let list_subparser: SubparserFuncListType<Term> = &|input| {
                    parse_list(
                        ",",
                        Subparser {
                            fun: term_subparser,
                        },
                        input,
                    )
                };
                let (terms, newrest) = parse_bracketed_list(
                    ListSubparser {
                        fun: list_subparser,
                    },
                    rest,
                );
                (Formula::atom(Pred::pred(p, &terms)), newrest)
            }
            [p, rest @ ..] if p != "(" => (Formula::atom(Pred::pred(p, &[])), rest),
            _ => panic!("parse_atom"),
        }
    }

    fn _parse_pred_formula_inner<'a>(input: &'a [String]) -> PartialParseResult<'a, Formula<Pred>> {
        parse_formula(
            Formula::_infix_parser,
            Formula::_atom_parser,
            &vec![], // Bound Variables
            input,
        )
    }

    pub fn parse(input: &str) -> Formula<Pred> {
        generic_parser(Formula::_parse_pred_formula_inner, input)
    }
}

#[cfg(test)]
mod parse_pred_formula_tests {

    use super::*;

    #[test]
    fn test_parse_pred_formula_variables() {
        let input = "F(x) /\\ G(d(y)) ==> p(13, w)";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::imp(
            Formula::and(
                Formula::atom(Pred::pred("F", &[Term::var("x")])),
                Formula::atom(Pred::pred("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            Formula::atom(Pred::pred("p", &[Term::constant("13"), Term::var("w")])),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_quantifiers() {
        // Remember that quantifiers bind looser than any connective.
        let input = "forall y w. F(RED) /\\ exists RED BLUE. G(d(y))";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::forall(
            "y",
            Formula::forall(
                "w",
                Formula::and(
                    Formula::atom(Pred::pred("F", &[Term::var("RED")])),
                    Formula::exists(
                        "RED",
                        Formula::exists(
                            "BLUE",
                            Formula::atom(Pred::pred("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );

        assert_eq!(result, desired);
    }
}

// ### Printing ###
impl Formula<Pred> {
    pub fn pprint<W: Write>(&self, dest: &mut W) -> () {
        let pfn: fn(&mut W, u32, &Pred) -> () = Pred::print_pred;
        self.pprint_general(dest, &pfn);
        write(dest, "\n");
    }
}

#[cfg(test)]
mod test_print_pred_formula {
    use super::*;

    #[test]
    fn test_print_pred_formula_variables() {
        let input = Formula::imp(
            Formula::and(
                Formula::atom(Pred::pred("F", &[Term::var("x")])),
                Formula::atom(Pred::pred("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            Formula::atom(Pred::pred("p", &[Term::constant("13"), Term::var("w")])),
        );

        let mut output = Vec::new();
        input.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<F(x) /\\ G(d(y)) ==> p(13, w)>>\n";
        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_pred_formula_quantifiers() {
        let input = Formula::forall(
            "y",
            Formula::forall(
                "w",
                Formula::and(
                    Formula::atom(Pred::pred("F", &[Term::var("RED")])),
                    Formula::exists(
                        "RED",
                        Formula::exists(
                            "BLUE",
                            Formula::atom(Pred::pred("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );
        let mut output = Vec::new();
        input.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<forall y w. F(RED) /\\ (exists RED BLUE. G(d(y)))>>\n";
        assert_eq!(output, desired);
    }
}
