// ### First
// Order Logic ###
// AST specific parsing/printing functions for first-order (aka predicate) logic.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use crate::first_order_logic_grammar::{PredFormulaParser, TermParser};
use crate::formula::{Formula, FormulaSet};
use crate::token::INFIX_RELATION_SYMBOLS;
use crate::token::{Lexer, LexicalError, Token};

use lalrpop_util::ParseError;

// Term
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

impl Term {
    pub fn var(name: &str) -> Term {
        Term::Var(String::from(name))
    }

    pub fn fun(name: &str, terms: &[Term]) -> Term {
        Term::Fun(String::from(name), terms.to_owned())
    }

    pub fn constant(name: &str) -> Term {
        Term::fun(name, &[])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn add(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("+"), vec![t1.to_owned(), t2.to_owned()])
    }

    pub fn unary_minus(t: &Term) -> Term {
        Term::Fun(String::from("-"), vec![t.to_owned()])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("-"), vec![t1.to_owned(), t2.to_owned()])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("*"), vec![t1.to_owned(), t2.to_owned()])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn div(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("/"), vec![t1.to_owned(), t2.to_owned()])
    }

    pub fn exp(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("^"), vec![t1.to_owned(), t2.to_owned()])
    }
    // The inclusion of infix list constructor is a bit
    // surprising and seems to imply that domains will often
    // be closed under cartesian products.
    pub fn cons(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("::"), vec![t1.to_owned(), t2.to_owned()])
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

// TERM PARSING
impl Term {
    pub fn parset(input: &str) -> Result<Term, ParseError<usize, Token, LexicalError>> {
        let lexer = Lexer::new(input);
        let parser = TermParser::new();
        parser.parse(lexer)
    }
}

#[cfg(test)]
mod term_parse_tests {

    use super::*;

    #[test]
    fn test_parse_term_constant() {
        let input = "42";

        let result = Term::parset(input).unwrap();

        let desired = Term::constant("42");

        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_term_variable() {
        let input = "x";

        let result = Term::parset(input).unwrap();

        let desired = Term::var("x");

        assert_eq!(result, desired);
    }
    #[test]
    fn test_parse_term_simple_0() {
        let input = "42+x";

        let result = Term::parset(input).unwrap();

        let desired = Term::add(&Term::constant("42"), &Term::var("x"));

        assert_eq!(result, desired);
    }
    #[test]
    fn test_parse_term_simple_1() {
        let input = "(13+x)/A";

        let result = Term::parset(input).unwrap();

        let desired = Term::div(
            &Term::add(&Term::constant("13"), &Term::var("x")),
            &Term::var("A"),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parset_0() {
        let result = Term::parset("foo(X, the_meaning(), Z)").unwrap();
        let desired = Term::fun(
            "foo",
            &[
                Term::var("X"),
                Term::fun("the_meaning", &[]),
                Term::var("Z"),
            ],
        );
        assert_eq!(result, desired);
    }

    fn test_parset_1() {
        let result = Term::parset("bar(B, baz(C))").unwrap();
        let desired = Term::fun(
            "bar",
            &[Term::var("B"), Term::fun("baz", &[Term::var("C")])],
        );
        assert_eq!(result, desired);
    }
}

// TERM Pretty
impl Term {
    fn get_term(prec: u32, term: &Term) -> String {
        match term {
            Term::Var(x) => x.to_owned(),
            Term::Fun(op, args) if op == "^" && args.len() == 2 => {
                Term::get_infix_term(true, prec, 24, "^", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "/" && args.len() == 2 => {
                Term::get_infix_term(true, prec, 22, " / ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "*" && args.len() == 2 => {
                Term::get_infix_term(false, prec, 20, " * ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "-" && args.len() == 2 => {
                Term::get_infix_term(true, prec, 18, " - ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "+" && args.len() == 2 => {
                Term::get_infix_term(false, prec, 16, " + ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "::" && args.len() == 2 => {
                Term::get_infix_term(false, prec, 14, "::", &args[0], &args[1])
            }
            Term::Fun(f, args) => Term::get_fargs(f, args),
        }
    }

    fn get_fargs(f: &str, args: &[Term]) -> String {
        // Print a prefix predicate/function application e.g. R(x, y, ...), or f(u, v, ...)

        let mut result = String::from(f);

        match &args {
            [] => {}
            // Dont' print parens for constants and propositions
            [head, rest @ ..] => {
                result.push('(');
                result.push_str(&Term::get_term(0, head));

                for term in rest {
                    result.push_str(", ");
                    result.push_str(&Term::get_term(0, term));
                }
                result.push(')');
            }
        }

        result
    }

    fn get_infix_term(
        is_left: bool,
        old_prec: u32,
        new_prec: u32,
        symbol: &str,
        term1: &Term,
        term2: &Term,
    ) -> String {
        let mut result = String::new();
        if old_prec > new_prec {
            result.push('(')
        }
        result.push_str(&Term::get_term(
            if is_left { new_prec } else { new_prec + 1 },
            term1,
        ));

        result.push_str(symbol);
        result.push_str(&Term::get_term(
            if is_left { new_prec + 1 } else { new_prec },
            term2,
        ));

        if old_prec > new_prec {
            result.push(')');
        }

        result
    }

    pub fn pretty(&self) -> String {
        let mut result = String::from("<<|");
        result.push_str(&Term::get_term(0, self));
        result.push_str("|>>");
        result
    }
    pub fn pprint(&self) {
        println!("{}", self.pretty());
    }
}

#[cfg(test)]
mod term_print_tests {

    use super::*;

    #[test]
    fn test_print_term_simple_1() {
        let term = Term::div(
            &Term::add(&Term::constant("13"), &Term::var("x")),
            &Term::var("A"),
        );

        let output = term.pretty();

        let desired = "<<|(13 + x) / A|>>";

        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_term_simple_2() {
        let term = Term::sub(
            &Term::mul(
                &Term::var("apples"),
                &Term::unary_minus(&Term::var("oranges")),
            ),
            &Term::constant("42"),
        );

        let output = term.pretty();
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

        let output = term.pretty();
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
    pub fn new(name: &str, terms: &[Term]) -> Pred {
        // Convenience constructor for `Pred`s.
        Pred {
            name: String::from(name),
            terms: terms.to_owned(),
        }
    }

    fn pretty(_prec: u32, Pred { name, terms }: &Pred) -> String {
        if INFIX_RELATION_SYMBOLS.contains(&name.as_str()) && terms.len() == 2 {
            Term::get_infix_term(false, 12, 12, &format!(" {name} "), &terms[0], &terms[1])
        } else {
            Term::get_fargs(name, terms)
        }
    }
}

#[cfg(test)]
mod pred_print_tests {

    use super::*;

    #[test]
    fn print_pred_test_prefix() {
        let pred = Pred::new(
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
        let output = Pred::pretty(0, &pred);
        let desired = "R(V, apples::oranges::42, 19)";
        assert_eq!(output, desired);
    }

    #[test]
    fn print_pred_test_infix() {
        let pred = Pred::new(
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
        let output = Pred::pretty(0, &pred);
        let desired = "apples::oranges::42 <= 19";
        assert_eq!(output, desired);
    }
}

// Formula Parsing

impl Formula<Pred> {
    pub fn parse(input: &str) -> Result<Formula<Pred>, ParseError<usize, Token, LexicalError>> {
        let lexer = Lexer::new(input);
        let parser = PredFormulaParser::new();
        parser.parse(lexer)
    }
}

#[cfg(test)]
mod parse_pred_formula_tests {

    use super::*;

    #[test]
    fn test_parse_pred_basics() {
        let result = Formula::<Pred>::parse("bar(X, Z)").unwrap();
        let pred = Pred::new("bar", &[Term::var("X"), Term::var("Z")]);
        let desired = Formula::atom(&pred);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables() {
        let input = "F(x) /\\ G(d(y)) ==> p(13, w)";

        let result = Formula::<Pred>::parse(input).unwrap();

        let desired = Formula::imp(
            &Formula::and(
                &Formula::atom(&Pred::new("F", &[Term::var("x")])),
                &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            &Formula::atom(&Pred::new("p", &[Term::constant("13"), Term::var("w")])),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_2() {
        let input = "(R(Y, X) /\\ false)";

        let result = Formula::<Pred>::parse(input).unwrap();

        let desired = Formula::and(
            &Formula::atom(&Pred::new("R", &[Term::var("Y"), Term::var("X")])),
            &Formula::False,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_3() {
        let input = "(Y = X)";
        let result = Formula::<Pred>::parse(input).unwrap();
        let desired = Formula::atom(&Pred::new("=", &[Term::var("Y"), Term::var("X")]));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_4() {
        let _ = env_logger::builder().is_test(true).try_init();
        let input = "Y = X \\/ false";

        let result = Formula::<Pred>::parse(input).unwrap();

        let desired = Formula::or(
            &Formula::atom(&Pred::new("=", &[Term::var("Y"), Term::var("X")])),
            &Formula::False,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_5() {
        let _ = env_logger::builder().is_test(true).try_init();
        let input = "(Y = X \\/ false)";

        let result = Formula::<Pred>::parse(input).unwrap();

        let desired = Formula::or(
            &Formula::atom(&Pred::new("=", &[Term::var("Y"), Term::var("X")])),
            &Formula::False,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_quantifiers() {
        let input = "forall y w. (F(RED) /\\ exists RED BLUE. G(d(y)))";

        let result = Formula::<Pred>::parse(input).unwrap();

        let desired = Formula::forall(
            "y",
            &Formula::forall(
                "w",
                &Formula::and(
                    &Formula::atom(&Pred::new("F", &[Term::var("RED")])),
                    &Formula::exists(
                        "RED",
                        &Formula::exists(
                            "BLUE",
                            &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );

        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_ea_quantified() {
        let result = Formula::<Pred>::parse("exists X. forall Y. bar(X, Y)").unwrap();
        let desired = Formula::exists(
            "X",
            &Formula::forall(
                "Y",
                &Formula::atom(&Pred::new("bar", &[Term::var("X"), Term::var("Y")])),
            ),
        );

        assert_eq!(result, desired);
    }

    #[test]
    fn test_simple_infix() {
        let input = "~(x = y)";
        let result = Formula::<Pred>::parse(input).unwrap();
        let desired = Formula::not(&Formula::atom(&Pred::new(
            "=",
            &[Term::var("x"), Term::var("y")],
        )));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_more_quantifiers() {
        let input = "forall x. (~(x = 0) ==> exists y. x * y = 1)";

        let desired = Formula::forall(
            "x",
            &Formula::imp(
                &Formula::not(&Formula::atom(&Pred::new(
                    "=",
                    &[Term::var("x"), Term::fun("0", &[])],
                ))),
                &Formula::exists(
                    "y",
                    &Formula::atom(&Pred::new(
                        "=",
                        &[
                            Term::fun("*", &[Term::var("x"), Term::var("y")]),
                            Term::fun("1", &[]),
                        ],
                    )),
                ),
            ),
        );

        let result = Formula::<Pred>::parse(input).unwrap();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_more_quantifiers_2() {
        let result = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = W").unwrap();
        let desired = Formula::exists(
            "X",
            &Formula::exists(
                "Y",
                &Formula::atom(&Pred::new(
                    "=",
                    &[
                        Term::fun("foo", &[Term::var("X"), Term::var("Y"), Term::var("Z")]),
                        Term::var("W"),
                    ],
                )),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_more_quantifiers_3() {
        let result = Formula::<Pred>::parse("exists z. exists y. ~(false)").unwrap();
        let desired = Formula::exists("z", &Formula::exists("y", &Formula::not(&Formula::False)));
        assert_eq!(result, desired);
    }
}

// Formula Printing
impl Formula<Pred> {
    pub fn pretty(&self) -> String {
        let atom_pretty: fn(u32, &Pred) -> String = Pred::pretty;
        self.pretty_general(&atom_pretty)
    }

    pub fn pprint(&self) {
        println!("{}", self.pretty())
    }
}

#[cfg(test)]
mod test_print_pred_formula {
    use super::*;

    #[test]
    fn test_print_pred_formula_variables() {
        let input = Formula::imp(
            &Formula::and(
                &Formula::atom(&Pred::new("F", &[Term::var("x")])),
                &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            &Formula::atom(&Pred::new("p", &[Term::constant("13"), Term::var("w")])),
        );

        let output = input.pretty();
        let desired = "<<F(x) /\\ G(d(y)) ==> p(13, w)>>";
        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_pred_formula_quantifiers() {
        let input = Formula::forall(
            "y",
            &Formula::forall(
                "w",
                &Formula::and(
                    &Formula::atom(&Pred::new("F", &[Term::var("RED")])),
                    &Formula::exists(
                        "RED",
                        &Formula::exists(
                            "BLUE",
                            &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );
        let output = input.pretty();
        let desired = "<<forall y w. (F(RED) /\\ (exists RED BLUE. G(d(y))))>>";
        assert_eq!(output, desired);
    }
}

#[derive(Clone)]
// Eval
pub struct Language {
    pub func: HashMap<String, usize>,
    pub rel: HashMap<String, usize>,
}

type FuncType<DomainType> = dyn Fn(&[DomainType]) -> DomainType;
type RelType<DomainType> = dyn Fn(&[DomainType]) -> bool;

pub struct Interpretation<DomainType: Hash + Clone + Eq + Debug + 'static> {
    // Need a lifetime parameter due to the trait bounds in func/rel.
    lang: Language,
    domain: HashSet<DomainType>,
    func: HashMap<String, Box<FuncType<DomainType>>>,
    rel: HashMap<String, Box<RelType<DomainType>>>,
}

impl<DomainType: Hash + Clone + Eq + Debug> Interpretation<DomainType> {
    pub fn new(
        lang: &Language,
        domain: HashSet<DomainType>,
        funcs: HashMap<String, Box<FuncType<DomainType>>>,
        rels: HashMap<String, Box<RelType<DomainType>>>,
    ) -> Interpretation<DomainType> {
        // Notice:  Takes ownership of some parameters.
        // Wrap each function in a check for the correct arity.
        // Note that this does not check, e.g. that the domain is closed under
        // operations in funcs.
        let mut safe_funcs = HashMap::<String, Box<FuncType<DomainType>>>::new();
        for (name, f) in funcs {
            let name_clone = name.clone();
            let domain_clone = domain.clone();
            let arity = lang.func[&name];
            let safe_f = move |input: &[DomainType]| -> DomainType {
                assert_eq!(
                    input.len(),
                    arity,
                    "Function {} has arity {} but was passed {} arguments",
                    name_clone,
                    arity,
                    input.len()
                );
                for arg in input {
                    assert!(
                        domain_clone.contains(arg),
                        "In evaluating function {}, Value {:?} is not in domain",
                        name_clone,
                        &arg
                    );
                }
                f(input)
            };
            safe_funcs.insert(name.clone(), Box::new(safe_f));
        }
        let mut safe_rels = HashMap::<String, Box<RelType<DomainType>>>::new();
        for (name, r) in rels {
            let name_clone = name.clone();
            let domain_clone = domain.clone();
            let arity = lang.rel[&name];
            let safe_r = move |input: &[DomainType]| -> bool {
                assert_eq!(
                    input.len(),
                    arity,
                    "Relation {} has arity {} but was passed {} arguments",
                    name_clone,
                    arity,
                    input.len()
                );
                for arg in input {
                    assert!(
                        domain_clone.contains(arg),
                        "In evaluating relation {}
                        Value {:?} is not in domain",
                        name_clone,
                        &arg
                    );
                }
                r(input)
            };
            safe_rels.insert(name.clone(), Box::new(safe_r));
        }

        Interpretation {
            lang: lang.clone(),
            domain,
            func: safe_funcs,
            rel: safe_rels,
        }
    }
}

mod test_utils {

    use super::*;

    pub type DomainType = u32;

    pub fn get_test_interpretation() -> Interpretation<DomainType> {
        fn _foo(input: &[DomainType]) -> DomainType {
            std::cmp::min(input[0] + input[1] + input[2], 60)
        }

        fn _bar(input: &[DomainType]) -> bool {
            (input[0] + input[1]) % 2 == 0
        }

        fn _equals(input: &[DomainType]) -> bool {
            input[0] == input[1]
        }

        fn _the_meaning(_input: &[DomainType]) -> DomainType {
            42
        }

        let lang: Language = Language {
            func: HashMap::from([(String::from("foo"), 3), (String::from("the_meaning"), 0)]),
            rel: HashMap::from([(String::from("bar"), 2), (String::from("="), 2)]),
        };

        let domain: HashSet<DomainType> = (1..=60).collect();
        let funcs: HashMap<String, Box<FuncType<DomainType>>> = HashMap::from([
            (
                String::from("foo"),
                Box::new(_foo) as Box<FuncType<DomainType>>,
            ),
            (
                String::from("the_meaning"),
                Box::new(_the_meaning) as Box<FuncType<DomainType>>,
            ),
        ]);
        let rels: HashMap<String, Box<RelType<DomainType>>> = HashMap::from([
            (
                String::from("bar"),
                Box::new(_bar) as Box<RelType<DomainType>>,
            ),
            (
                String::from("="),
                Box::new(_equals) as Box<RelType<DomainType>>,
            ),
        ]);

        Interpretation::new(&lang, domain, funcs, rels)
    }
}

#[cfg(test)]
mod interpretation_tests {

    use super::*;

    #[test]
    fn test_new_basic() {
        let m = test_utils::get_test_interpretation();
        assert_eq!(m.func["foo"](&[1, 3, 3]), 7);
        assert!(m.rel["bar"](&[3, 21]));
    }

    #[test]
    #[should_panic]
    fn test_new_panic_1() {
        // Should panic since foo is ternary.
        let m = test_utils::get_test_interpretation();
        m.func["foo"](&[1, 3]);
    }

    #[test]
    #[should_panic]
    fn test_new_panic_2() {
        // Should panic since foo is ternary.
        let m = test_utils::get_test_interpretation();
        m.func["foo"](&[1, 3, 3, 21]);
    }

    #[test]
    #[should_panic]
    fn test_new_panic_3() {
        // Should panic since 61 is not in the domain.
        let m = test_utils::get_test_interpretation();
        m.func["foo"](&[1, 61, 4]);
    }
}

// Partial Map from variable names to domain elements
// implemented as linked frames to allow for less
// copying.
pub struct FOValuation<'a, DomainType: Hash + Clone + Eq + Debug> {
    // Any new assignments for this frame
    frame: HashMap<String, DomainType>,
    // Pointer to the next frame
    next: Option<&'a FOValuation<'a, DomainType>>,
}

impl<'a, DomainType: Hash + Clone + Eq + Debug> FOValuation<'a, DomainType> {
    // Maybe implement this later.
    #[allow(clippy::new_without_default)]
    pub fn new() -> FOValuation<'a, DomainType> {
        FOValuation {
            frame: HashMap::new(),
            next: None,
        }
    }

    pub fn from(data: &HashMap<String, DomainType>) -> FOValuation<'a, DomainType> {
        // Todo, implement coming from general iter.
        FOValuation {
            frame: data.clone(),
            next: None,
        }
    }

    fn set(&self, name: String, val: DomainType) -> FOValuation<'_, DomainType> {
        let frame = HashMap::from([(name, val)]);
        let next = Some(self);
        FOValuation { frame, next }
    }

    fn get(&self, name: &str) -> Option<DomainType> {
        // First try local frame, and failing that, defer
        // to `next` FOValuation (if any).
        if let Some(value) = self.frame.get(name) {
            let cloned: DomainType = value.clone();
            return Some(cloned);
        }
        match self.next {
            Some(valuation) => valuation.get(name),
            None => None,
        }
    }
}

// ### Term Evaluation ###
impl Term {
    pub fn eval<DomainType: Hash + Clone + Eq + Debug>(
        &self,
        m: &Interpretation<DomainType>,
        v: &FOValuation<DomainType>,
    ) -> DomainType {
        match self {
            Term::Var(name) => match v.get(&name.to_string()) {
                Some(val) => val,
                None => panic!("FOValuation not defined on variable {name:?}."),
            },
            Term::Fun(name, args) => {
                let func_box: &FuncType<DomainType> = &m.func[&name.to_string()];
                let vals: Vec<DomainType> = args.iter().map(|term| term.eval(m, v)).collect();
                (*func_box)(&vals)
            }
        }
    }
}

#[cfg(test)]
mod test_term_eval {
    use super::*;

    #[test]
    fn test_term_eval_simple() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("X".to_string(), 14),
            ("Y".to_string(), 1),
            ("Z".to_string(), 2),
        ]);
        let v = FOValuation::from(&map);

        let var_x = Term::var("X");
        let var_z = Term::var("Z");

        assert_eq!(var_x.eval(&m, &v), 14);
        assert_eq!(var_z.eval(&m, &v), 2);

        let t = Term::parset("foo(X, the_meaning(), Z)").unwrap();
        assert_eq!(t.eval(&m, &v), 58);
    }
}

impl Pred {
    pub fn eval<DomainType: Hash + Clone + Eq + Debug>(
        &self,
        m: &Interpretation<DomainType>,
        v: &FOValuation<DomainType>,
    ) -> bool {
        let rel_box: &RelType<DomainType> = &m.rel[&self.name];
        let vals: Vec<DomainType> = self.terms.iter().map(|term| term.eval(m, v)).collect();
        (*rel_box)(&vals)
    }
}

#[cfg(test)]
mod test_pred_eval {

    use super::*;

    #[test]
    fn test_pred_eval_simple() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("X".to_string(), 14),
            ("Y".to_string(), 1),
            ("Z".to_string(), 2),
            ("W".to_string(), 14),
        ]);
        let v = FOValuation::from(&map);

        let t = Term::parset("foo(X, the_meaning(), Z)").unwrap();

        let pred_1 = Pred::new("bar", &[t.clone(), Term::var("Y")]);
        assert!(!pred_1.eval(&m, &v)); // 58 + 1 % 2 = 0 is false
        let pred_2 = Pred::new("bar", &[t, Term::var("X")]);
        assert!(pred_2.eval(&m, &v)); // 58 + 14 % 2 == 0 is true
        let pred_3 = Pred::new("=", &[Term::var("Y"), Term::var("X")]);
        assert!(!pred_3.eval(&m, &v)); // 1 == 14 is false
        let pred_4 = Pred::new("=", &[Term::var("W"), Term::var("X")]);
        assert!(pred_4.eval(&m, &v)); // 14 == 14 is true
    }
}

// ### Formula Evaluation ###
impl Formula<Pred> {
    pub fn eval<DomainType: Hash + Clone + Eq + Debug>(
        &self,
        m: &Interpretation<DomainType>,
        v: &FOValuation<DomainType>,
    ) -> bool {
        let pred_atom_eval = |pred: &Pred| -> bool { pred.eval(m, v) };

        // TODO the clone inside of the for loops of the quantifiers could get expensive.
        // Find a better way. Partial functions like Z3 arrays?

        let forall_eval = |var: &str, subformula: &Formula<Pred>| -> bool {
            for val in &m.domain {
                let v_ext = v.set(var.to_string(), val.clone()); // (var |-> val)v
                if !subformula.eval(m, &v_ext) {
                    return false;
                }
            }
            true
        };

        let exists_eval = |var: &str, subformula: &Formula<Pred>| -> bool {
            for val in &m.domain {
                let v_ext = v.set(var.to_string(), val.clone()); // (var |-> val)v
                if subformula.eval(m, &v_ext) {
                    return true;
                }
            }
            false
        };

        self.eval_core(&pred_atom_eval, &forall_eval, &exists_eval)
    }
}

#[cfg(test)]
mod test_formula_eval {

    use super::*;

    #[test]
    fn test_formula_eval_simple() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("X".to_string(), 14),
            ("Y".to_string(), 1),
            ("Z".to_string(), 2),
        ]);
        let v = FOValuation::from(&map);

        let formula_1 = Formula::<Pred>::parse("bar(X, Z)").unwrap();
        assert!(formula_1.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_1() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([("Z".to_string(), 2)]);
        let v = FOValuation::from(&map);

        let formula_1 = Formula::<Pred>::parse("exists X. bar(X, Z)").unwrap();

        assert!(formula_1.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_2() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("U".to_string(), 43),
            ("Z".to_string(), 42),
            ("W".to_string(), 58),
        ]);
        let v = FOValuation::from(&map);

        let formula_1 = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = W").unwrap();

        // A Solution exists.
        assert!(formula_1.eval(&m, &v));

        let formula_2 = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = U").unwrap();
        // No Solution exists in (1..=60)
        assert!(!formula_2.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_3() {
        let m = test_utils::get_test_interpretation();
        let v = FOValuation::new();

        let formula_ae = Formula::<Pred>::parse("forall X. exists Y. bar(X, Y)").unwrap();
        assert!(formula_ae.eval(&m, &v));
        let formula_ea = Formula::<Pred>::parse("exists X. forall Y. bar(X, Y)").unwrap();
        assert!(!formula_ea.eval(&m, &v));
    }
}

// Term Variables
type Instantiation = HashMap<String, Term>;

impl Term {
    fn get_variables_for_termlist(terms: &[Term]) -> HashSet<String> {
        terms
            .iter()
            .fold(HashSet::new(), |acc, term| &acc | &term.variables())
    }

    fn variables(&self) -> HashSet<String> {
        // Theorem (Harrison 3.1)
        // if `t: Term` and if `v, v': FOValuation` such that
        // for all x in t.variables() we have v(x) == v'(x), then
        // t.eval(M, v) == t.eval(M, v') for any `M: Interpretation`.
        match self {
            Term::Var(name) => HashSet::from([name.clone()]),
            Term::Fun(_name, terms) => Term::get_variables_for_termlist(terms),
        }
    }

    fn functions(&self) -> HashSet<(String, usize)> {
        // Return functions with arities.
        match self {
            Term::Var(_) => HashSet::new(),
            Term::Fun(name, args) => args
                .iter()
                .fold(HashSet::from([(name.clone(), args.len())]), |acc, arg| {
                    &acc | &arg.functions()
                }),
        }
    }

    pub fn subst(&self, inst: &Instantiation) -> Term {
        // Substitute Terms for Vars throughout according to `inst`.
        //
        // Lemma (Harrison 3.5)
        // For any `t: Term`, `inst: Instatiation`, `M: Interpretation`
        // `v: FOValuation`, we have
        // t.subst(inst).eval(M, v) = t.eval(M, {x |-> inst(x).eval(M, v)})
        match self {
            Term::Var(x) => inst.get(x).unwrap_or(&Term::var(x)).clone(),
            Term::Fun(name, args) => {
                let new_args: Vec<Term> = args.iter().map(|term| term.subst(inst)).collect();
                Term::fun(name, &new_args)
            }
        }
    }

    pub fn variant(var: &str, vars: &HashSet<String>) -> String {
        // Add primes ("'") to `var` until the result is not in `vars`.
        if vars.contains(var) {
            let guess = format!("{var}'");
            Term::variant(&guess, vars)
        } else {
            var.to_owned()
        }
    }
}

#[cfg(test)]
mod test_term_variables {

    use crate::utils::{slice_to_set_of_owned, slice_to_vec_of_owned};

    use super::*;

    #[test]
    fn test_get_variables_for_termlist() {
        let term1 = Term::parset("foo(A)").unwrap();
        let term2 = Term::parset("B").unwrap();
        let term3 = Term::parset("bar(B, baz(C))").unwrap();
        let input = vec![term1, term2, term3];

        let result = Term::get_variables_for_termlist(&input);
        assert_eq!(result, slice_to_set_of_owned(&["A", "B", "C"]),);
    }

    #[test]
    fn test_variables() {
        let input = Term::parset("F1(foo(A), B, bar(B, baz(C)))").unwrap();
        let result = input.variables();
        assert_eq!(result, slice_to_set_of_owned(&["A", "B", "C"]),);
    }

    #[test]
    fn test_functions() {
        let input = Term::parset("F1(foo(A), B, bar(13, baz(C)))").unwrap();
        let result = input.functions();
        let desired_names = slice_to_vec_of_owned(&["F1", "foo", "bar", "baz", "13"]);
        let desired_arities = vec![3, 1, 2, 1, 0];
        let desired: HashSet<(String, usize)> =
            desired_names.into_iter().zip(desired_arities).collect();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_subst() {
        let input = Term::parset("F1(foo(A), B, bar(B, baz(C)))").unwrap();
        let t1 = Term::var("S");
        let t2 = Term::fun("B", &[Term::var("v")]);
        let inst = Instantiation::from([("B".to_string(), t1), ("C".to_string(), t2)]);
        let result = input.subst(&inst);
        let desired = Term::parset("F1(foo(A), S, bar(S, baz(B(v))))").unwrap();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_variant() {
        let existing: HashSet<String> = slice_to_set_of_owned(&["a", "b", "b'"]);

        let var = "c";
        let result = Term::variant(var, &existing);
        assert_eq!(result, "c");

        let var = "a";
        let result = Term::variant(var, &existing);
        assert_eq!(result, "a'");

        let var = "b";
        let result = Term::variant(var, &existing);
        assert_eq!(result, "b''");
    }
}

impl Pred {
    fn variables(&self) -> HashSet<String> {
        Term::get_variables_for_termlist(&self.terms)
    }

    fn functions(&self) -> HashSet<(String, usize)> {
        self.terms
            .iter()
            .fold(HashSet::new(), |acc, term| &acc | &term.functions())
    }
}

// ### Variables ###
impl Formula<Pred> {
    fn variables(&self) -> HashSet<String> {
        match self {
            Formula::True | Formula::False => HashSet::new(),
            Formula::Atom(pred) => pred.variables(),
            Formula::Not(p) => p.variables(),
            Formula::And(p, q) | Formula::Or(p, q) | Formula::Imp(p, q) | Formula::Iff(p, q) => {
                &p.variables() | &q.variables()
            }
            Formula::Forall(var, p) | Formula::Exists(var, p) => {
                let mut vars = p.variables();
                vars.insert(var.clone());
                vars
            }
        }
    }

    pub fn free_variables(&self) -> HashSet<String> {
        // Theorem (Harrison 3.2)
        // If `p: Formula<Pred>` and if `v, v': FOValuation` such that
        // for all x in p.free_variables()  we have v(x) == v'(x), then
        // p.eval(M, v) == p.eval(M, v') for any `M: Interpretation.
        //
        // Corollary (Harrision 3.3)
        // If `p: Formula<Pred>` and p.free_variables() == {}, then
        // p.eval(M, v) == p.eval(M, v') for any `M: Interpretation`
        // and any `v, v': FOValuation`.
        match self {
            Formula::True | Formula::False => HashSet::new(),
            Formula::Atom(pred) => pred.variables(),
            Formula::Not(p) => p.free_variables(),
            Formula::And(p, q) | Formula::Or(p, q) | Formula::Imp(p, q) | Formula::Iff(p, q) => {
                &p.free_variables() | &q.free_variables()
            }
            Formula::Forall(var, p) | Formula::Exists(var, p) => {
                let mut vars = p.free_variables();
                vars.remove(var);
                vars
            }
        }
    }

    fn functions(&self) -> HashSet<(String, usize)> {
        let combine = |pred: &Pred, agg: HashSet<(String, usize)>| -> HashSet<(String, usize)> {
            &pred.functions() | &agg
        };
        self.over_atoms(&combine, HashSet::new())
    }

    fn generalize(&self) -> Formula<Pred> {
        // The universal closure of `formula`.

        let mut sorted: Vec<String> = self.free_variables().iter().cloned().collect();
        sorted.sort();
        sorted
            .into_iter()
            .fold(self.clone(), |formula, var| Formula::forall(&var, &formula))
    }

    fn subst_quant(
        inst: &Instantiation,
        quant_const: &QuantConstructor,
        var: &String,
        formula: &Formula<Pred>,
    ) -> Formula<Pred> {
        // Helper function for `subst`.  Does substitution in `formula` according to `inst`
        // and re-attaches the quantifier for `quant_const`, making sure to change the
        // variable of quantification (if necessary) to one not occuring free in the resulting
        // formula (substitution result).
        let mut other_vars = formula.free_variables();
        other_vars.remove(var);
        let mut would_be_captured = false;
        for free_var in other_vars {
            // Try apply?
            let image_free_variables = inst
                .get(&free_var)
                .unwrap_or(&Term::var(&free_var))
                .variables();
            if image_free_variables.contains(var) {
                would_be_captured = true;
                break;
            }
        }
        let new_var = if would_be_captured {
            let mut tmp_inst = inst.clone();
            tmp_inst.remove(var);
            let free_variables = formula.subst(&tmp_inst).free_variables();
            Term::variant(var, &free_variables)
        } else {
            var.clone()
        };

        let mut new_inst = inst.clone();
        new_inst.insert(var.clone(), Term::var(&new_var));
        quant_const(&new_var, &formula.subst(&new_inst))
    }

    pub fn subst(&self, inst: &Instantiation) -> Formula<Pred> {
        // Substitute Terms for Vars throughout according to `inst`, swapping in
        // fresh variables of quantification when necessary to avoid unwanted
        // capture.
        //
        // Theorem (Harrision 3.7)
        // For any `p: Formula<Pred>`, `inst: Instatiation`, `M: Interpretation`
        // `v: FOValuation`, we have
        // p.subst(inst).eval(M, v) = p.eval(M, {x |-> inst(x).eval(M, v)})
        //
        // Corollary (Harrison 3.8)
        // If a formula is valid, then so is any substitution instance.
        match self {
            Formula::False | Formula::True => self.clone(),
            Formula::Atom(Pred { name, terms }) => {
                let new_args: Vec<Term> = terms.iter().map(|term| term.subst(inst)).collect();
                Formula::atom(&Pred::new(name, &new_args))
            }
            Formula::Not(p) => Formula::not(&p.subst(inst)),
            Formula::And(p, q) => Formula::and(&p.subst(inst), &q.subst(inst)),
            Formula::Or(p, q) => Formula::or(&p.subst(inst), &q.subst(inst)),
            Formula::Imp(p, q) => Formula::imp(&p.subst(inst), &q.subst(inst)),
            Formula::Iff(p, q) => Formula::iff(&p.subst(inst), &q.subst(inst)),
            Formula::Forall(x, p) => Formula::subst_quant(inst, &Formula::forall, x, p),
            Formula::Exists(x, p) => Formula::subst_quant(inst, &Formula::exists, x, p),
        }
    }
}

#[cfg(test)]
mod test_formula_variables {

    use super::*;
    use crate::utils::slice_to_set_of_owned;
    use crate::utils::slice_to_vec_of_owned;

    #[test]
    fn test_formula_variables() {
        let formula =
            Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W, Z) = U").unwrap();
        let result_all = formula.variables();
        let desired_all = slice_to_set_of_owned(&["U", "W", "X", "Z"]);
        assert_eq!(result_all, desired_all);
    }

    #[test]
    fn test_formula_free_variables() {
        let formula =
            Formula::<Pred>::parse("forall X. (X = W ==> exists W. foo(X, W, Z) = U)").unwrap();
        let result_free = formula.free_variables();
        let desired_free = slice_to_set_of_owned(&["U", "W", "Z"]);
        assert_eq!(result_free, desired_free);
    }

    #[test]
    fn test_formula_functions() {
        let formula =
            Formula::<Pred>::parse("forall X. f(X) = W ==> exists W. foo(X, bar(13), Z) = U")
                .unwrap();
        let result = formula.functions();
        let desired_names = slice_to_vec_of_owned(&["f", "foo", "bar", "13"]);
        let desired_arities = vec![1, 3, 1, 0];
        let desired: HashSet<(String, usize)> =
            desired_names.into_iter().zip(desired_arities).collect();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_formula_functions_2() {
        let formula_string = "R(F(y, r)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) \\/ exists z. ~M(F(z, w))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = formula.functions();
        let desired_names = slice_to_vec_of_owned(&["F", "f_w", "G"]);
        let desired_arities = vec![2, 1, 2];
        let desired: HashSet<(String, usize)> =
            desired_names.into_iter().zip(desired_arities).collect();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_generalize() {
        let formula =
            Formula::<Pred>::parse("forall X. (X = W ==> exists W. foo(X, W) = U)").unwrap();
        let result = formula.generalize();
        let desired =
            Formula::<Pred>::parse("forall W U X. (X = W ==> exists W. foo(X, W) = U)").unwrap();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_subst() {
        let formula = Formula::<Pred>::parse("R(foo(X, W, Z), U)").unwrap();
        let inst = Instantiation::from([
            ("W".to_string(), Term::parset("Z").unwrap()),
            ("Z".to_string(), Term::parset("U").unwrap()),
        ]);
        let result = formula.subst(&inst);
        let desired = Formula::<Pred>::parse("R(foo(X, Z, U), U)").unwrap();
        assert_eq!(result, desired);

        let formula =
            Formula::<Pred>::parse("forall X. (X = W ==> exists W. foo(X, W, Z) = U)").unwrap();
        let inst = Instantiation::from([("W".to_string(), Term::parset("bar(X, R)").unwrap())]);
        let result = formula.subst(&inst);
        let desired =
            Formula::<Pred>::parse("forall X'. (X' = bar(X, R) ==> exists W. foo(X', W, Z) = U)")
                .unwrap();
        assert_eq!(result, desired);

        let formula =
            Formula::<Pred>::parse("forall X. (X = W ==> exists W. foo(X, W, Z) = U)").unwrap();
        let inst = Instantiation::from([("X".to_string(), Term::parset("W").unwrap())]);
        let result = formula.subst(&inst);
        let desired = formula;
        assert_eq!(result, desired);
    }
}

type QuantConstructor = dyn Fn(&str, &Formula<Pred>) -> Formula<Pred>;
type BinopConstructor = dyn Fn(&Formula<Pred>, &Formula<Pred>) -> Formula<Pred>;
// Normal Forms
impl Formula<Pred> {
    fn fo_simplify_step(formula: &Formula<Pred>) -> Formula<Pred> {
        // In addition to core simplifications, removes quantifiers `Qx` in
        // formulas `Qx.p` when quantified formulas `p` do not contain
        // free occurences of `x`.
        match formula {
            Formula::Forall(x, p) | Formula::Exists(x, p) => {
                if p.free_variables().contains(x) {
                    formula.clone()
                } else {
                    *p.clone()
                }
            }
            _ => Formula::psimplify_step(formula),
        }
    }

    pub fn simplify(self: &Formula<Pred>) -> Formula<Pred> {
        self.simplify_recursive(&Formula::fo_simplify_step)
    }

    fn nnf(&self) -> Formula<Pred> {
        // Negation normal form
        // NOTE:  Harrison actually doesn't simplify first (but makes
        // sure to simplify in the final definition of prenex form.
        self.simplify().raw_nnf()
    }

    fn pull_quantifiers(formula: &Formula<Pred>) -> Formula<Pred> {
        // Assumes that `formula` is of the form `<binop>(p, q)` where `p, q` are
        // already in prenex form.
        // Recursively pulls out all quantifiers leading `p` and `q` to result in
        // a prenex formula.
        match formula {
            Formula::And(r, s) => match (*r.clone(), *s.clone()) {
                (Formula::Forall(x, p), Formula::Forall(y, q)) => Formula::pullq(
                    true,
                    true,
                    formula,
                    &Formula::forall,
                    &Formula::and,
                    &x,
                    &y,
                    &p,
                    &q,
                ),

                (Formula::Forall(x, p), q) => Formula::pullq(
                    true,
                    false,
                    formula,
                    &Formula::forall,
                    &Formula::and,
                    &x,
                    &x,
                    &p,
                    &q,
                ),

                (p, Formula::Forall(y, q)) => Formula::pullq(
                    false,
                    true,
                    formula,
                    &Formula::forall,
                    &Formula::and,
                    &y,
                    &y,
                    &p,
                    &q,
                ),
                (Formula::Exists(x, p), q) => Formula::pullq(
                    true,
                    false,
                    formula,
                    &Formula::exists,
                    &Formula::and,
                    &x,
                    &x,
                    &p,
                    &q,
                ),
                (p, Formula::Exists(y, q)) => Formula::pullq(
                    false,
                    true,
                    formula,
                    &Formula::exists,
                    &Formula::and,
                    &y,
                    &y,
                    &p,
                    &q,
                ),
                _ => formula.clone(),
            },

            Formula::Or(r, s) => match (*r.clone(), *s.clone()) {
                (Formula::Exists(x, p), Formula::Exists(y, q)) => Formula::pullq(
                    true,
                    true,
                    formula,
                    &Formula::exists,
                    &Formula::or,
                    &x,
                    &y,
                    &p,
                    &q,
                ),
                (Formula::Forall(x, p), q) => Formula::pullq(
                    true,
                    false,
                    formula,
                    &Formula::forall,
                    &Formula::or,
                    &x,
                    &x,
                    &p,
                    &q,
                ),

                (p, Formula::Forall(y, q)) => Formula::pullq(
                    false,
                    true,
                    formula,
                    &Formula::forall,
                    &Formula::or,
                    &y,
                    &y,
                    &p,
                    &q,
                ),

                (Formula::Exists(x, p), q) => Formula::pullq(
                    true,
                    false,
                    formula,
                    &Formula::exists,
                    &Formula::or,
                    &x,
                    &x,
                    &p,
                    &q,
                ),

                (p, Formula::Exists(y, q)) => Formula::pullq(
                    false,
                    true,
                    formula,
                    &Formula::exists,
                    &Formula::or,
                    &y,
                    &y,
                    &p,
                    &q,
                ),
                _ => formula.clone(),
            },

            _ => formula.clone(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn pullq(
        sub_left: bool,
        sub_right: bool,
        formula: &Formula<Pred>,
        quant_const: &QuantConstructor,
        binop_const: &BinopConstructor,
        x: &str,
        y: &str,
        p: &Formula<Pred>,
        q: &Formula<Pred>,
    ) -> Formula<Pred> {
        // Helper function mutually recursive with `pull_quantifiers`.  Handles
        // the move of a single quantifier (of type corresponding to `quant_const`)
        // occuring at the heads of one or both  sides of a binary operation
        // (corresponding to (binop_const)).  `formula` is the entire formula.
        // Which side(s) the quantifiers are from is represented by `sub_left`/`sub_right`
        // `x`/`y` are the corresponding variables (if applicable) for the
        // left/right sides, and `p, q` are the corresponding
        // quantified formulas (if applicable)
        // for the left/right sides.
        let z = Term::variant(x, &formula.free_variables());
        let p_new = if sub_left {
            let inst = Instantiation::from([(x.to_owned(), Term::Var(z.clone()))]);
            p.subst(&inst)
        } else {
            p.clone()
        };
        let q_new = if sub_right {
            let inst = Instantiation::from([(y.to_owned(), Term::Var(z.clone()))]);
            q.subst(&inst)
        } else {
            q.clone()
        };
        quant_const(&z, &Formula::pull_quantifiers(&binop_const(&p_new, &q_new)))
    }

    fn raw_prenex(&self) -> Formula<Pred> {
        // Assumes `formula` is in NNF.
        match self {
            Formula::Forall(x, p) => Formula::forall(x, &p.raw_prenex()),
            Formula::Exists(x, p) => Formula::exists(x, &p.raw_prenex()),
            Formula::And(p, q) => {
                Formula::pull_quantifiers(&Formula::and(&p.raw_prenex(), &q.raw_prenex()))
            }
            Formula::Or(p, q) => {
                Formula::pull_quantifiers(&Formula::or(&p.raw_prenex(), &q.raw_prenex()))
            }
            _ => self.clone(),
        }
    }

    pub fn pnf(&self) -> Formula<Pred> {
        // Result should be of the form `Q_1 x_1 ... Q_n x_n. p`
        // where `p` is a quantifier-free formula in negation normal form.
        self.simplify().nnf().raw_prenex()
    }
}

#[cfg(test)]
mod normal_form_tests {

    use super::*;

    #[test]
    fn test_simplify_step() {
        let formula_string = "exists w. forall z. G(z)";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = Formula::fo_simplify_step(&formula);
        let desired_string = "forall z. G(z)";
        let desired = Formula::<Pred>::parse(desired_string).unwrap();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_simplify() {
        let formula_string = "Y = X /\\ false \\/ (false ==> R(Z))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let desired = Formula::True;
        assert_eq!(formula.simplify(), desired);

        let formula_string =
            "forall x. ((true ==> (R(x) <=> false)) ==> exists z. exists y. ~(K(y) \\/ false))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let desired_string = "forall x. (~R(x) ==> exists y. ~K(y))";
        let desired = Formula::<Pred>::parse(desired_string).unwrap();
        assert_eq!(formula.simplify(), desired);

        let formula_string = "exists w. forall z. G(z)";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let desired_string = "forall z. G(z)";
        let desired = Formula::<Pred>::parse(desired_string).unwrap();
        assert_eq!(formula.simplify(), desired);
    }

    #[test]
    fn test_raw_prenex() {
        let formula_string = "F(x) /\\ forall y. exists w. (G(y, z) \\/ exists z. ~F(z))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = formula.raw_prenex();
        let desired_string = "forall y. exists w. exists z'. (F(x) /\\ (G(y, z) \\/ ~F(z')))";
        let desired = Formula::<Pred>::parse(desired_string).unwrap();
        assert_eq!(result, desired);

        // let formula_string = "(exists x. F(x, z)) ==> (exists w forall z. ~G(z, x))";
        let formula_string = "(forall x. ~F(x, z)) \\/ (forall z. ~G(z, x))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = formula.raw_prenex();
        let desired_string = "forall x'. forall z'. (~F(x', z) \\/ ~G(z', x))";
        let desired = Formula::<Pred>::parse(desired_string).unwrap();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_pnf() {
        let formula_string = "exists x. F(x, z) ==> exists w. forall z. ~G(z, x)";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = formula.pnf();
        let desired_string = "forall x'. forall z'. (~F(x', z) \\/ ~G(z', x))";
        let desired = Formula::<Pred>::parse(desired_string).unwrap();
        assert_eq!(result, desired);
    }
}

// Skolemization

impl Formula<Pred> {
    fn skolem_1(
        formula: &Formula<Pred>,
        functions: &HashSet<String>,
    ) -> (Formula<Pred>, HashSet<String>) {
        match formula {
            Formula::Exists(y, p) => {
                // Here is where we introduce the new skolem constant (if `formula` has no free
                // variables) / skolem function of any free variables.
                let free = formula.free_variables();
                let func_name_candidate = if free.is_empty() {
                    format!("c_{y}")
                } else {
                    format!("f_{y}")
                };
                let func_name = Term::variant(&func_name_candidate, functions);
                let mut new_functions = functions.clone();
                new_functions.insert(func_name.clone());
                let mut sorted = Vec::from_iter(free);
                sorted.sort();
                let vars: Vec<Term> = sorted.iter().map(|name| Term::var(name)).collect();
                let function_term = Term::fun(&func_name, &vars);
                let substituted = p.subst(&Instantiation::from([(y.to_owned(), function_term)]));
                Formula::skolem_1(&substituted, &new_functions)
            }
            Formula::Forall(y, p) => {
                let (inner, new_functions) = Formula::skolem_1(p, functions);
                (Formula::forall(y, &inner), new_functions)
            }
            Formula::And(p, q) => Formula::skolem_2(&Formula::and, p, q, functions),
            Formula::Or(p, q) => Formula::skolem_2(&Formula::or, p, q, functions),
            _ => (formula.clone(), functions.clone()),
        }
    }

    fn skolem_2(
        op: &BinopConstructor,
        p: &Formula<Pred>,
        q: &Formula<Pred>,
        functions_0: &HashSet<String>,
    ) -> (Formula<Pred>, HashSet<String>) {
        let (p_new, functions_1) = Formula::skolem_1(p, functions_0);
        let (q_new, functions_2) = Formula::skolem_1(q, &functions_1);
        (op(&p_new, &q_new), functions_2)
    }

    fn askolemize(&self) -> Formula<Pred> {
        // We could keep the arities to allow for distinct
        // functions of the same name (but different arities).
        // I'm going to see how far we can get w/o this since I think allowing
        // disctinct functions of the same name is pretty rare.
        let functions: HashSet<String> = self.functions().into_iter().map(|pair| pair.0).collect();

        // Note that Existential subformulas must occur "positively" for
        // this proceedure to return an equi-satisfiable result.
        // Else consider <<exists y. P(y) /\\ ~ exists z. P(z)>>
        // whose skolemization is the (satisfiable) P(a) /\\ P(b).
        // Traditionally one convers all the way to PNF first, but
        // this can lead to overly complex skolemized version, and
        // nnf is sufficient.
        Formula::skolem_1(&self.simplify().nnf(), &functions).0
    }

    fn remove_universal_quantifiers(&self) -> Formula<Pred> {
        // NOTE:   This should only be applied to formulas of the form
        // <<forall x_1 .. x_n. phi>> (where phi is quantifier free)
        match self {
            Formula::Forall(_, p) => p.remove_universal_quantifiers(),
            _ => self.clone(),
        }
    }

    pub fn skolemize(&self) -> Formula<Pred> {
        self.askolemize().pnf().remove_universal_quantifiers()
    }
}

#[cfg(test)]
mod skolemize_tests {

    use super::*;
    use crate::utils::slice_to_set_of_owned;

    #[test]
    fn test_skolem_1() {
        let formula_string = "R(F(n)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. (M(G(y, w)) \\/ exists z. ~M(F(z, w)))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = Formula::skolem_1(&formula, &slice_to_set_of_owned(&["f_w", "F", "G"]));
        let desired_formula_string =
            "R(F(n)) \\/ P(f_w(c_x())) /\\ forall r. forall y. (M(G(y, f_w'(y))) \\/ ~M(F(f_z(y), f_w'(y))))";
        let desired_formula = Formula::<Pred>::parse(desired_formula_string).unwrap();
        // Note that "c_n" is added to the functions even though it appears zero times
        // in the result.  This is because `n` does not appear in within the scope of
        // the quantifier `exists n`.
        let desired_functions =
            slice_to_set_of_owned(&["c_x", "f_w", "G", "F", "f_w'", "f_z", "c_n"]);
        assert_eq!(result, (desired_formula, desired_functions));
    }

    #[test]
    fn test_skolemize() {
        let formula_string = "R(F(y)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. (M(G(y, w)) \\/ exists z. ~M(F(z, w)))";
        let formula = Formula::<Pred>::parse(formula_string).unwrap();
        let result = formula.skolemize();
        let desired_formula_string =
            "R(F(y)) \\/ P(f_w(c_x())) /\\ (M(G(y', f_w'(y'))) \\/ ~M(F(f_z(y'), f_w'(y'))))";
        let desired_formula = Formula::<Pred>::parse(desired_formula_string).unwrap();
        assert_eq!(result, desired_formula);
    }
}

// Herbrand methods
//

#[derive(Debug, PartialEq, Clone)]
pub enum HerbrandResult {
    ValidityProved(HashSet<Vec<Term>>),
    InvalidityProved,
    BoundReached(usize),
}

impl Formula<Pred> {
    #[allow(clippy::type_complexity)]
    fn herbrand_functions(
        formula: &Formula<Pred>,
    ) -> (HashSet<(String, usize)>, HashSet<(String, usize)>) {
        let (mut constants, functions): (HashSet<(String, usize)>, HashSet<(String, usize)>) =
            formula
                .functions()
                .into_iter()
                .partition(|pair| pair.1 == 0);

        if constants.is_empty() {
            constants = HashSet::from([("c".to_string(), 0)]);
        }
        (constants, functions)
    }
    pub fn ground_terms(
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        level: usize,
        cache: &mut HashMap<(usize, usize), BTreeSet<Vec<Term>>>,
    ) -> HashSet<Term> {
        if level == 0 {
            return constants
                .iter()
                .map(|(name, _arity)| Term::fun(name, &[]))
                .collect();
        }
        functions
            .iter()
            .map(|(name, arity)| {
                // Get set of all applications of this function to args of the
                // apprpriate level and length.
                Formula::ground_tuples(constants, functions, level - 1, arity.to_owned(), cache)
                    .iter()
                    .map(|tuple| Term::fun(name, tuple))
                    .collect::<HashSet<Term>>()
            })
            .fold(HashSet::new(), |x, y| &x | &y)
    }

    fn get_all_appends(
        vectors: &BTreeSet<Vec<Term>>,
        elements: &HashSet<Term>,
    ) -> BTreeSet<Vec<Term>> {
        // Return all vectors that result in prepending an element from `elements`
        // to a vector from `vectors`.
        elements
            .iter()
            .map(|element| {
                vectors
                    .iter()
                    .map(|vector| {
                        let mut clone = vector.clone();
                        clone.push(element.clone());
                        clone
                    })
                    .collect::<BTreeSet<Vec<Term>>>()
            })
            .fold(BTreeSet::new(), |x, y| &x | &y)
    }

    pub fn ground_tuples(
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        level: usize,
        size: usize,
        cache: &mut HashMap<(usize, usize), BTreeSet<Vec<Term>>>,
    ) -> BTreeSet<Vec<Term>> {
        // Todo:  Use a cache!

        // Return all tuples of length `size` of ground terms having exactly `level` number of
        // function call instances summing over all terms in the tuple.
        if size == 0 {
            return if level == 0 {
                BTreeSet::from([Vec::new()])
            } else {
                BTreeSet::from([])
            };
        }

        if cache.contains_key(&(level, size)) {
            return cache.get(&(level, size)).unwrap().clone();
        }
        // Consider each choice of num functions in last element.
        let result = (0..=level)
            .map(|k| {
                let last_element_options = Formula::ground_terms(constants, functions, k, cache);
                let up_to_last_element_options =
                    Formula::ground_tuples(constants, functions, level - k, size - 1, cache);
                // Note we append instead of prepend since it seems cheaper.
                Formula::get_all_appends(&up_to_last_element_options, &last_element_options)
            })
            .fold(BTreeSet::new(), |x, y| &x | &y);

        cache.insert((level, size), result.clone());

        result
    }

    fn make_instantiation(free_variables: &[String], terms: &[Term]) -> Instantiation {
        // Map corresponding `free_variables` to `terms`.
        assert_eq!(free_variables.len(), terms.len());
        free_variables
            .iter()
            .enumerate()
            .map(|(idx, var)| (var.to_owned(), terms[idx].clone()))
            .collect()
    }

    fn subst_tuple_into_formulaset(
        formula: &FormulaSet<Pred>,
        free_variables: &[String],
        tuple: &[Term],
    ) -> FormulaSet<Pred> {
        let instantiation: Instantiation = Formula::make_instantiation(free_variables, tuple);
        // First substitute in the ground instances for `instantiation`.
        Formula::subst_in_formulaset(formula, &instantiation)
    }

    #[allow(clippy::too_many_arguments)]
    fn herbrand_loop<SatTest, GroundInstancesAugmenter>(
        // NOTE could put the first 6 of these parameters into a struct `HerbloopContext`
        // since they don't change...
        augment_ground_instances: &GroundInstancesAugmenter,
        sat_test: SatTest,
        formula: &FormulaSet<Pred>,
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        free_variables: &Vec<String>,
        next_level: usize,
        ground_instances_so_far: &FormulaSet<Pred>,
        mut tuples_tried: HashSet<Vec<Term>>,
        mut tuples_left_at_level: BTreeSet<Vec<Term>>,
        max_depth: usize,
        tuple_cache: &mut HashMap<(usize, usize), BTreeSet<Vec<Term>>>,
    ) -> HerbrandResult
    where
        SatTest: Fn(&FormulaSet<Pred>) -> bool,
        GroundInstancesAugmenter: Fn(&FormulaSet<Pred>, &FormulaSet<Pred>) -> FormulaSet<Pred>,
    {
        // `augment_ground_instances`:  Updates ground_instances_so_far for a given tuple
        // of ground terms. Note that this will depend on whether a FormulaSet<Pred> is a
        // DNF vs CNF representation.
        //
        // `sat_test`: test for whether a `FormulaSet<Pred>` is satisfiable. Note that this will
        // depend on whether a FormulaSet<Pred> is a DNF vs CNF representation.
        //
        // `formula`: A `FormulaSet<Pred>` representation of the target formula to be tested for
        // satisfiability.
        //
        // `constants`/`functions`; all constants/functions in the Herbrand universe for
        // `formula`.
        //
        // `free_variables`: all free variables in `formula`.
        //
        // `next_level`: the next level of ground tuples to consider
        // after `tuples_left_at_level` is depleated.
        //
        // `ground_instances_so_far`:   A FormulaSet<Pred> representation of the set of
        // all ground instances that we are checking for joint satisfiability.
        //
        // `tuple_tried`: Tuples of terms that we have so far converted to ground instances
        // (`FormulaSet<Pred>`s specifically) and added to the `ground_instances_so_far`.
        //
        // `tuples_left_at_level`: Remaining tuples for the last `next_level` computed
        // which we have yet to convert and incorporate into `ground_instances_so_far`.
        //
        // `max_depth`: A level of term nesting after which to give up.
        //
        // `tuple_cache` A DP cache of all tuples for (size, level) if computed already.

        if tuples_left_at_level.is_empty() {
            if next_level > max_depth {
                return HerbrandResult::BoundReached(max_depth);
            }

            println!("Generating tuples for next level {}", next_level);

            // Note that these tuples are always of the same length = free_variables.len()
            let new_tuples = Formula::ground_tuples(
                constants,
                functions,
                next_level,
                free_variables.len(),
                tuple_cache,
            );

            if new_tuples.is_empty() {
                return HerbrandResult::InvalidityProved;
            }

            Formula::herbrand_loop(
                augment_ground_instances,
                sat_test,
                formula,
                constants,
                functions,
                free_variables,
                next_level + 1,
                ground_instances_so_far,
                tuples_tried,
                new_tuples,
                max_depth,
                tuple_cache,
            )
        } else {
            let next_tuple: Vec<Term> = tuples_left_at_level.pop_first().unwrap();

            // First substitute in the ground instances for `instantiation`.
            let new_ground_instance: FormulaSet<Pred> =
                Formula::subst_tuple_into_formulaset(formula, free_variables, &next_tuple);

            println!(
                "Adding new formula to set: {:?}",
                Formula::formulaset_to_cnf(new_ground_instance.clone()).pretty()
            );
            let augmented_instances =
                augment_ground_instances(&new_ground_instance, ground_instances_so_far);
            tuples_tried.insert(next_tuple.clone());
            if !sat_test(&augmented_instances) {
                HerbrandResult::ValidityProved(tuples_tried)
            } else {
                Formula::herbrand_loop(
                    augment_ground_instances,
                    sat_test,
                    formula,
                    constants,
                    functions,
                    free_variables,
                    next_level,
                    &augmented_instances,
                    tuples_tried,
                    tuples_left_at_level,
                    max_depth,
                    tuple_cache,
                )
            }
        }
    }

    fn subst_in_formulaset(
        formula: &FormulaSet<Pred>,
        instantiation: &Instantiation,
    ) -> FormulaSet<Pred> {
        formula
            .iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|literal| literal.subst(instantiation))
                    .collect()
            })
            .collect()
    }

    fn augement_dnf_formulaset(
        new_formula: &FormulaSet<Pred>,
        ground_instances_so_far: &FormulaSet<Pred>,
    ) -> FormulaSet<Pred> {
        // Combine with existing ground instances
        let aggregate = Formula::_set_distrib_and_over_or(new_formula, ground_instances_so_far);
        Formula::_strip_contradictory(&aggregate)
    }

    #[allow(clippy::too_many_arguments)]
    fn gilmore_loop(
        formula: &FormulaSet<Pred>,
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        free_variables: &Vec<String>,
        next_level: usize,
        ground_instances_so_far: &FormulaSet<Pred>,
        tuples_tried: HashSet<Vec<Term>>,
        tuples_left_at_level: BTreeSet<Vec<Term>>,
        max_depth: usize,
    ) -> HerbrandResult {
        // USES DNF FormulaSet representations throughout.
        //
        fn sat_test(formula: &FormulaSet<Pred>) -> bool {
            !formula.is_empty()
        }

        let tuple_cache = &mut HashMap::new();

        Formula::herbrand_loop(
            &Formula::augement_dnf_formulaset,
            |formula: &FormulaSet<Pred>| !formula.is_empty(),
            formula,
            constants,
            functions,
            free_variables,
            next_level,
            ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
            max_depth,
            tuple_cache,
        )
    }

    pub fn gilmore(formula: &Formula<Pred>, max_depth: usize) -> HerbrandResult {
        // Tautology test by checking whether the negation is unsatisfiable.
        // USES DNF FormulaSet representations throughout.

        // Note that it is important to generalize first, since `p valid iff ~p unsat` is true
        // only for ground formulas, ie. formulas with no free variables.

        let negation_skolemized = formula.generalize().negate().skolemize();
        let (constants, functions) = Formula::herbrand_functions(&negation_skolemized);
        let mut free_variables = Vec::from_iter(negation_skolemized.free_variables());
        free_variables.sort();
        // The following does a strip of clauses with contradictory literals,
        // so that the satisfiability is equivalent to being non-empty.
        // This is an invariant we maintain throughout, even as we add to the accumulator.
        let dnf_formula = negation_skolemized.dnf_formulaset();
        Formula::gilmore_loop(
            &dnf_formula,
            &constants,
            &functions,
            &free_variables,
            0,
            &FormulaSet::from([BTreeSet::new()]),
            HashSet::new(),
            BTreeSet::new(),
            max_depth,
        )
    }

    // Davis-Putnam approach
    //
    fn augment_cnf_formulaset(
        new_formula: &FormulaSet<Pred>,
        ground_instances_so_far: &FormulaSet<Pred>,
    ) -> FormulaSet<Pred> {
        // Simply conjoin all new CNF clauses.
        new_formula | ground_instances_so_far
    }

    #[allow(clippy::too_many_arguments)]
    fn dp_loop(
        formula: &FormulaSet<Pred>,
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        free_variables: &Vec<String>,
        next_level: usize,
        ground_instances_so_far: &FormulaSet<Pred>,
        tuples_tried: HashSet<Vec<Term>>,
        tuples_left_at_level: BTreeSet<Vec<Term>>,
        max_depth: usize,
    ) -> HerbrandResult {
        // USES CNF FormulaSet representations throughout.

        let tuple_cache = &mut HashMap::new();

        Formula::herbrand_loop(
            &Formula::augment_cnf_formulaset,
            Formula::dpll,
            formula,
            constants,
            functions,
            free_variables,
            next_level,
            ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
            max_depth,
            tuple_cache,
        )
    }

    fn _get_dp_unsat_core_cnf(
        formula: &FormulaSet<Pred>,
        free_variables: &Vec<String>,
        mut unknown: BTreeSet<Vec<Term>>,
        mut needed: BTreeSet<Vec<Term>>,
    ) -> HashSet<Vec<Term>> {
        // Find a minimal subset of tuples whose corresponding set of formulas are
        // inconsistent.
        // Note the following recursive invariant: The set of formulas corresponding to
        // `unknown U needed` is unsat.
        //
        if unknown.is_empty() {
            return HashSet::from_iter(needed);
        }
        let next = unknown.pop_first().unwrap();
        // If formulas for unknown U needed are still inconsistent, discard `next`.
        // Else add next to needed.

        // NOTE: Could pass this as an additional parameter to keep from having to build
        // it from scratch each time.
        let new_union = needed
            .union(&unknown)
            .map(|tuple| Formula::subst_tuple_into_formulaset(formula, free_variables, tuple))
            .fold(FormulaSet::new(), |acc, new| {
                Formula::augment_cnf_formulaset(&new, &acc)
            });

        if Formula::dpll(&new_union) {
            needed.insert(next);
        }
        Formula::_get_dp_unsat_core_cnf(formula, free_variables, unknown, needed)
    }

    pub fn davis_putnam(
        formula: &Formula<Pred>,
        get_unsat_core: bool,
        max_depth: usize,
    ) -> HerbrandResult {
        // Validity test by checking whether the negation is unsatisfiable.
        // USES CNF FormulaSet representations throughout.

        // Note that it is important to generalize first, since `p valid iff ~p unsat` is true
        // only for ground formulas, ie. formulas with no free variables.
        let negation_skolemized = formula.generalize().negate().skolemize();
        println!("Skolemized negation is {}", negation_skolemized.pretty());
        let (constants, functions) = Formula::herbrand_functions(&negation_skolemized);
        let mut free_variables = Vec::from_iter(negation_skolemized.free_variables());
        free_variables.sort();
        let cnf_formula = negation_skolemized.cnf_formulaset();

        let mut result = Formula::dp_loop(
            &cnf_formula,
            &constants,
            &functions,
            &free_variables,
            0,
            &FormulaSet::new(),
            HashSet::new(),
            BTreeSet::new(),
            max_depth,
        );
        match result.clone() {
            HerbrandResult::ValidityProved(mut tuples) => {
                if get_unsat_core {
                    tuples = Formula::_get_dp_unsat_core_cnf(
                        &cnf_formula,
                        &free_variables,
                        BTreeSet::from_iter(tuples),
                        BTreeSet::new(),
                    )
                }
                result = HerbrandResult::ValidityProved(tuples.clone());
                let unsat_formulas: HashSet<Formula<Pred>> = tuples
                    .iter()
                    .map(|tuple| {
                        Formula::subst_tuple_into_formulaset(&cnf_formula, &free_variables, tuple)
                    })
                    .map(Formula::formulaset_to_cnf)
                    .collect();

                println!(
                    "Found {} inconsistent ground instances of skolemized negation:",
                    unsat_formulas.len()
                );
                for form in unsat_formulas.iter() {
                    form.pprint();
                }
                println!("Formula is valid.");
            }

            HerbrandResult::InvalidityProved => {
                println!("Set of ground instances (of negation) was both finite and satisfiable.  Invalidity proved.");
            }
            HerbrandResult::BoundReached(bound) => {
                println!("After searching to bound depth {}, set of ground instances (of negation) is still satisfiable. Giving up.", bound);
            }
        }

        result
    }
}

#[cfg(test)]
mod herbrand_tests {

    use super::*;

    #[test]
    fn test_herbrand_functions() {
        let formula = Formula::<Pred>::parse("P(g(f(42, x)))").unwrap();
        let result = Formula::herbrand_functions(&formula);
        let desired_constants = HashSet::from([(String::from("42"), 0)]);
        let desired_functions = HashSet::from([(String::from("f"), 2), (String::from("g"), 1)]);
        assert_eq!(result, (desired_constants, desired_functions));

        let formula = Formula::<Pred>::parse("P(f(x))").unwrap();
        let result = Formula::herbrand_functions(&formula);
        let desired_constants = HashSet::from([(String::from("c"), 0)]);
        let desired_functions = HashSet::from([(String::from("f"), 1)]);
        assert_eq!(result, (desired_constants, desired_functions));
    }

    #[test]
    fn test_ground_terms() {
        let constants = HashSet::from([(String::from("42"), 0)]);
        let functions = HashSet::from([(String::from("f"), 2), (String::from("g"), 1)]);

        let empty_cache = HashMap::new();

        let level = 0;
        let result = Formula::ground_terms(&constants, &functions, level, &mut empty_cache.clone());
        let desired = HashSet::from([Term::constant("42")]);
        assert_eq!(result, desired);

        let level = 1;
        let result = Formula::ground_terms(&constants, &functions, level, &mut empty_cache.clone());
        let desired = HashSet::from([
            Term::parset("g(42)").unwrap(),
            Term::parset("f(42, 42)").unwrap(),
        ]);
        assert_eq!(result, desired);

        let level = 2;
        let result = Formula::ground_terms(&constants, &functions, level, &mut empty_cache.clone());
        let desired = HashSet::from([
            Term::parset("g(g(42))").unwrap(),
            Term::parset("g(f(42, 42))").unwrap(),
            Term::parset("f(g(42), 42)").unwrap(),
            Term::parset("f(42, g(42))").unwrap(),
            Term::parset("f(f(42, 42), 42)").unwrap(),
            Term::parset("f(42, f(42, 42))").unwrap(),
        ]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_all_appends() {
        let vectors: BTreeSet<Vec<Term>> = BTreeSet::from([
            vec![Term::parset("A").unwrap(), Term::parset("B").unwrap()],
            vec![Term::parset("C").unwrap(), Term::parset("D").unwrap()],
        ]);
        let elements: HashSet<Term> =
            HashSet::from([Term::parset("X").unwrap(), Term::parset("Y").unwrap()]);

        let result = Formula::get_all_appends(&vectors, &elements);

        let desired: BTreeSet<Vec<Term>> = BTreeSet::from([
            vec![
                Term::parset("A").unwrap(),
                Term::parset("B").unwrap(),
                Term::parset("X").unwrap(),
            ],
            vec![
                Term::parset("C").unwrap(),
                Term::parset("D").unwrap(),
                Term::parset("X").unwrap(),
            ],
            vec![
                Term::parset("A").unwrap(),
                Term::parset("B").unwrap(),
                Term::parset("Y").unwrap(),
            ],
            vec![
                Term::parset("C").unwrap(),
                Term::parset("D").unwrap(),
                Term::parset("Y").unwrap(),
            ],
        ]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_ground_tuples() {
        let constants = HashSet::from([(String::from("42"), 0)]);
        let functions = HashSet::from([(String::from("f"), 2), (String::from("g"), 1)]);

        let empty_cache = HashMap::new();
        let level = 0;
        let size = 0;
        let result: BTreeSet<Vec<Term>> = Formula::ground_tuples(
            &constants,
            &functions,
            level,
            size,
            &mut empty_cache.clone(),
        );
        let desired = BTreeSet::from([Vec::new()]);
        assert_eq!(result, desired);

        let level = 1;
        let size = 0;
        let result: BTreeSet<Vec<Term>> = Formula::ground_tuples(
            &constants,
            &functions,
            level,
            size,
            &mut empty_cache.clone(),
        );
        let desired = BTreeSet::from([]);
        assert_eq!(result, desired);

        let level = 0;
        let size = 2;
        let result: BTreeSet<Vec<Term>> = Formula::ground_tuples(
            &constants,
            &functions,
            level,
            size,
            &mut empty_cache.clone(),
        );
        let desired = BTreeSet::from([vec![
            Term::parset("42").unwrap(),
            Term::parset("42").unwrap(),
        ]]);
        assert_eq!(result, desired);

        let level = 2;
        let size = 1;
        let empty_cache = HashMap::new();
        let result: BTreeSet<Vec<Term>> = Formula::ground_tuples(
            &constants,
            &functions,
            level,
            size,
            &mut empty_cache.clone(),
        );
        let desired = BTreeSet::from([
            vec![Term::parset("f(g(42), 42)").unwrap()],
            vec![Term::parset("f(42, g(42))").unwrap()],
            vec![Term::parset("g(g(42))").unwrap()],
            vec![Term::parset("g(f(42, 42))").unwrap()],
            vec![Term::parset("f(f(42, 42), 42)").unwrap()],
            vec![Term::parset("f(42, f(42, 42))").unwrap()],
        ]);
        assert_eq!(result, desired);

        let level = 1;
        let size = 2;
        let result: BTreeSet<Vec<Term>> = Formula::ground_tuples(
            &constants,
            &functions,
            level,
            size,
            &mut empty_cache.clone(),
        );
        let desired = BTreeSet::from([
            vec![Term::parset("42").unwrap(), Term::parset("g(42)").unwrap()],
            vec![Term::parset("g(42)").unwrap(), Term::parset("42").unwrap()],
            vec![
                Term::parset("42").unwrap(),
                Term::parset("f(42, 42)").unwrap(),
            ],
            vec![
                Term::parset("f(42, 42)").unwrap(),
                Term::parset("42").unwrap(),
            ],
        ]);
        assert_eq!(result, desired);

        let level = 2;
        let size = 2;
        let result: BTreeSet<Vec<Term>> = Formula::ground_tuples(
            &constants,
            &functions,
            level,
            size,
            &mut empty_cache.clone(),
        );
        let desired = BTreeSet::from([
            // 0 and 2
            vec![
                Term::parset("42").unwrap(),
                Term::parset("f(g(42), 42)").unwrap(),
            ],
            vec![
                Term::parset("42").unwrap(),
                Term::parset("f(42, g(42))").unwrap(),
            ],
            vec![
                Term::parset("42").unwrap(),
                Term::parset("g(g(42))").unwrap(),
            ],
            vec![
                Term::parset("42").unwrap(),
                Term::parset("g(f(42, 42))").unwrap(),
            ],
            vec![
                Term::parset("42").unwrap(),
                Term::parset("f(f(42, 42), 42)").unwrap(),
            ],
            vec![
                Term::parset("42").unwrap(),
                Term::parset("f(42, f(42, 42))").unwrap(),
            ],
            // 1 and 1
            vec![
                Term::parset("g(42)").unwrap(),
                Term::parset("g(42)").unwrap(),
            ],
            vec![
                Term::parset("f(42, 42)").unwrap(),
                Term::parset("f(42, 42)").unwrap(),
            ],
            vec![
                Term::parset("g(42)").unwrap(),
                Term::parset("f(42, 42)").unwrap(),
            ],
            vec![
                Term::parset("f(42, 42)").unwrap(),
                Term::parset("g(42)").unwrap(),
            ],
            // 2 and 0
            vec![
                Term::parset("f(g(42), 42)").unwrap(),
                Term::parset("42").unwrap(),
            ],
            vec![
                Term::parset("f(42, g(42))").unwrap(),
                Term::parset("42").unwrap(),
            ],
            vec![
                Term::parset("g(g(42))").unwrap(),
                Term::parset("42").unwrap(),
            ],
            vec![
                Term::parset("g(f(42, 42))").unwrap(),
                Term::parset("42").unwrap(),
            ],
            vec![
                Term::parset("f(f(42, 42), 42)").unwrap(),
                Term::parset("42").unwrap(),
            ],
            vec![
                Term::parset("f(42, f(42, 42))").unwrap(),
                Term::parset("42").unwrap(),
            ],
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_herbloop() {
        fn augment_cnf_formulaset(
            new_formula: &FormulaSet<Pred>,
            ground_instances_so_far: &FormulaSet<Pred>,
        ) -> FormulaSet<Pred> {
            new_formula | ground_instances_so_far
        }

        fn sat_test(formula: &FormulaSet<Pred>) -> bool {
            // Just check for a random singleton clause.
            let target_clause = Formula::<Pred>::parse("~P(g(f(42, 42))) \\/  F(g(42))")
                .unwrap()
                .cnf_formulaset()
                .pop_first()
                .unwrap();
            !formula.contains(&target_clause)
        }

        let formula = Formula::<Pred>::parse("~P(g(x)) \\/ F(y)")
            .unwrap()
            .cnf_formulaset();

        let constants = HashSet::from([("42".to_string(), 0)]);
        let functions = HashSet::from([("f".to_string(), 2), ("g".to_string(), 1)]);

        let free_variables = vec!["x".to_string(), "y".to_string()];
        let next_level = 0;
        // CNF representation of True
        let ground_instances_so_far: FormulaSet<Pred> = BTreeSet::new();
        let tuples_tried: HashSet<Vec<Term>> = HashSet::new();
        let tuples_left_at_level: BTreeSet<Vec<Term>> = BTreeSet::new();
        let max_depth = 100;

        let empty_cache = HashMap::new();

        let result = Formula::herbrand_loop(
            &augment_cnf_formulaset,
            sat_test,
            &formula,
            &constants,
            &functions,
            &free_variables,
            next_level,
            &ground_instances_so_far,
            tuples_tried.clone(),
            tuples_left_at_level.clone(),
            max_depth,
            &mut empty_cache.clone(),
        );

        let tuples = match result {
            HerbrandResult::ValidityProved(tuples) => tuples,
            _ => panic!("Expected Validity proved in this test"),
        };

        let level_0_size_2 = HashSet::from_iter(Formula::ground_tuples(
            &constants,
            &functions,
            0,
            2,
            &mut empty_cache.clone(),
        ));
        let level_1_size_2 = HashSet::from_iter(Formula::ground_tuples(
            &constants,
            &functions,
            1,
            2,
            &mut empty_cache.clone(),
        ));
        let level_2_size_2 = HashSet::from_iter(Formula::ground_tuples(
            &constants,
            &functions,
            2,
            2,
            &mut empty_cache.clone(),
        ));
        let all_size_2 = &(&level_0_size_2 | &level_1_size_2) | &level_2_size_2;

        assert!(tuples.is_subset(&all_size_2));
        assert!(level_0_size_2.is_subset(&tuples));
        assert!(level_1_size_2.is_subset(&tuples));

        // Start at level 2:
        let result_2 = Formula::herbrand_loop(
            &augment_cnf_formulaset,
            sat_test,
            &formula,
            &constants,
            &functions,
            &free_variables,
            2,
            &ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
            max_depth,
            &mut empty_cache.clone(),
        );

        let tuples_2 = match result_2 {
            HerbrandResult::ValidityProved(tuples) => tuples,
            _ => panic!("Expected Validity proved in this test"),
        };

        assert!(tuples_2.is_subset(&level_2_size_2));
    }

    #[test]
    fn test_gilmore_loop() {
        let formula = Formula::<Pred>::parse("~P(g(x)) /\\ P(y)")
            .unwrap()
            .dnf_formulaset();

        let constants = HashSet::from([("42".to_string(), 0)]);
        let functions = HashSet::from([("f".to_string(), 2), ("g".to_string(), 1)]);

        let free_variables = vec!["x".to_string(), "y".to_string()];
        let next_level = 0;
        // DNF representation of True
        let ground_instances_so_far: FormulaSet<Pred> = BTreeSet::from([BTreeSet::new()]);
        let tuples_tried: HashSet<Vec<Term>> = HashSet::new();
        let tuples_left_at_level: BTreeSet<Vec<Term>> = BTreeSet::new();
        let max_depth = 100;

        let result = Formula::gilmore_loop(
            &formula,
            &constants,
            &functions,
            &free_variables,
            next_level,
            &ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
            max_depth,
        );

        let tuples = match result {
            HerbrandResult::ValidityProved(tuples) => tuples,
            _ => panic!("Expected Validity proved in this test"),
        };

        assert!(tuples.contains(&vec![
            Term::parset("42").unwrap(),
            Term::parset("g(42)").unwrap()
        ]));
    }

    #[test]
    fn test_gilmore() {
        let formula = Formula::<Pred>::parse("exists x. forall y. (P(x) ==> P(y))").unwrap();
        let max_depth = 100;
        let result = Formula::gilmore(&formula, max_depth);
        let tuples = match result {
            HerbrandResult::ValidityProved(tuples) => tuples,
            _ => panic!("Expected Validity proved in this test"),
        };
        assert!((2..=3).contains(&tuples.len()));
    }

    #[test]
    fn test_gilmore_2() {
        // (Not valid)
        let formula = Formula::<Pred>::parse("forall x. (P(x) \\/ ~P(x))").unwrap();
        let result = Formula::gilmore(&formula, 10);
        assert!(matches!(result, HerbrandResult::ValidityProved(_)));
    }

    #[test]
    fn test_dp_loop() {
        let formula = Formula::<Pred>::parse("~P(g(x)) /\\ P(y)")
            .unwrap()
            .cnf_formulaset();

        let constants = HashSet::from([("42".to_string(), 0)]);
        let functions = HashSet::from([("f".to_string(), 2), ("g".to_string(), 1)]);

        let free_variables = vec!["x".to_string(), "y".to_string()];
        let next_level = 0;
        // CNF representation of True
        let ground_instances_so_far: FormulaSet<Pred> = BTreeSet::new();
        let tuples_tried: HashSet<Vec<Term>> = HashSet::new();
        let tuples_left_at_level: BTreeSet<Vec<Term>> = BTreeSet::new();

        let max_depth = 100;

        let result = Formula::dp_loop(
            &formula,
            &constants,
            &functions,
            &free_variables,
            next_level,
            &ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
            max_depth,
        );
        let tuples = match result {
            HerbrandResult::ValidityProved(tuples) => tuples,
            _ => panic!("Expected Validity proved in this test"),
        };

        assert!(tuples.contains(&vec![
            Term::parset("42").unwrap(),
            Term::parset("g(42)").unwrap()
        ]));
    }

    // #[test]
    fn test_get_dp_unsat_core() {
        let formula = Formula::<Pred>::parse("P(x) /\\ ~P(f_y(x))")
            .unwrap()
            .cnf_formulaset();
        let free_variables = vec!["x".to_string()];
        let unknown = BTreeSet::from([
            vec![Term::parset("f_y(c)").unwrap()],
            vec![Term::parset("g(f_y(c))").unwrap()],
            vec![Term::parset("g(c)").unwrap()],
            vec![Term::parset("(c)").unwrap()],
            vec![Term::parset("d").unwrap()],
        ]);
        let needed = BTreeSet::new();

        let result: HashSet<Vec<Term>> =
            Formula::_get_dp_unsat_core_cnf(&formula, &free_variables, unknown, needed);

        let desired = HashSet::from([
            vec![Term::parset("f_y(c)").unwrap()],
            vec![Term::parset("c").unwrap()],
        ]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_davis_putnam_simple() {
        let formula = Formula::<Pred>::parse("exists x. forall y. (P(x) ==> P(y))").unwrap();
        let result = Formula::davis_putnam(&formula, false, 10);
        assert!(matches!(result, HerbrandResult::ValidityProved(_)));
    }

    #[test]
    fn test_davis_putnam_complex() {
        let string = "(forall x y. exists z. forall w. (P(x) /\\ Q(y) ==> R(z) /\\ U(w))) ==> 
            (exists x y. (P(x) /\\ Q(y))) ==> (exists z. R(z))";
        let formula = Formula::<Pred>::parse(string).unwrap();
        let result = Formula::davis_putnam(&formula, false, 10);
        assert!(matches!(result, HerbrandResult::ValidityProved(_)));
    }

    #[test]
    fn test_davis_putnam_complex_unsat_core() {
        let string = "(forall x y. exists z. forall w. (P(x) /\\ Q(y) ==> R(z) /\\ U(w))) ==> 
            (exists x y. (P(x) /\\ Q(y))) ==> (exists z. R(z))";
        let formula = Formula::<Pred>::parse(string).unwrap();
        let result = Formula::davis_putnam(&formula, true, 10);
        let tuples = match result {
            HerbrandResult::ValidityProved(tuples) => tuples,
            _ => panic!("Expected Validity proved in this test"),
        };
        assert_eq!(tuples.len(), 2);
    }

    #[test]
    fn test_davis_putnam_bound_reached() {
        // (Not valid)
        let formula =
            Formula::<Pred>::parse("forall boy. exists girl. Loves(girl, friend(boy))").unwrap();
        let result = Formula::davis_putnam(&formula, false, 10);
        assert_eq!(result, HerbrandResult::BoundReached(10));
    }

    #[test]
    fn test_davis_putnam_invalidity_proved_no_free_variables_in_skolemized() {
        // (Not valid)
        let formula = Formula::<Pred>::parse("forall x. P(f(x))").unwrap();
        let result = Formula::davis_putnam(&formula, false, 10);
        assert_eq!(result, HerbrandResult::InvalidityProved);
    }

    #[test]
    fn test_davis_putnam_invalidity_proved_relational() {
        // (Not valid)
        let formula = Formula::<Pred>::parse("exists x. (P(x, y) \\/ P(y, x))").unwrap();
        let result = Formula::davis_putnam(&formula, false, 10);
        assert_eq!(result, HerbrandResult::InvalidityProved);
    }
}
