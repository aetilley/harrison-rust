// Formula<T> class and Formula<T>-specific parsing/printing functions
// that do *not* depend on T.  See propositional_logic and first_order_logic
// files for specific parsing/printing functions that specify T.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use priority_queue::PriorityQueue;

//### Formula AST ###
#[derive(Debug, PartialEq, Clone, PartialOrd, Eq, Ord, Hash)]
pub enum Formula<T: Clone + Debug + Hash + Eq + Ord> {
    False,
    True,
    Atom(T),
    Not(Box<Formula<T>>),
    And(Box<Formula<T>>, Box<Formula<T>>),
    Or(Box<Formula<T>>, Box<Formula<T>>),
    Imp(Box<Formula<T>>, Box<Formula<T>>),
    Iff(Box<Formula<T>>, Box<Formula<T>>),
    Forall(String, Box<Formula<T>>),
    Exists(String, Box<Formula<T>>),
}

// General Builders and utilities.
impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    pub fn atom(t: &T) -> Formula<T> {
        Formula::Atom(t.to_owned())
    }

    pub fn not(formula: &Formula<T>) -> Formula<T> {
        Formula::Not(Box::new(formula.to_owned()))
    }

    pub fn and(formula1: &Formula<T>, formula2: &Formula<T>) -> Formula<T> {
        Formula::And(Box::new(formula1.to_owned()), Box::new(formula2.to_owned()))
    }

    pub fn or(formula1: &Formula<T>, formula2: &Formula<T>) -> Formula<T> {
        Formula::Or(Box::new(formula1.to_owned()), Box::new(formula2.to_owned()))
    }

    pub fn imp(formula1: &Formula<T>, formula2: &Formula<T>) -> Formula<T> {
        Formula::Imp(Box::new(formula1.to_owned()), Box::new(formula2.to_owned()))
    }

    pub fn iff(formula1: &Formula<T>, formula2: &Formula<T>) -> Formula<T> {
        Formula::Iff(Box::new(formula1.to_owned()), Box::new(formula2.to_owned()))
    }

    pub fn forall(var: &str, formula: &Formula<T>) -> Formula<T> {
        Formula::Forall(String::from(var), Box::new(formula.to_owned()))
    }

    pub fn exists(var: &str, formula: &Formula<T>) -> Formula<T> {
        Formula::Exists(String::from(var), Box::new(formula.to_owned()))
    }

    // NOTE:  The following might be better off as methods.

    pub fn get_imp_ops(formula: &Formula<T>) -> (Formula<T>, Formula<T>) {
        if let Formula::Imp(op1, op2) = formula {
            (*op1.clone(), *op2.clone())
        } else {
            panic!("Expected Formula::Imp, received {formula:?}.");
        }
    }

    pub fn antecedent(imp_formula: &Formula<T>) -> Formula<T> {
        Formula::get_imp_ops(imp_formula).0
    }

    pub fn consequent(imp_formula: &Formula<T>) -> Formula<T> {
        Formula::get_imp_ops(imp_formula).1
    }

    pub fn on_atoms<F: Fn(&T) -> Formula<T>>(&self, map: &F) -> Formula<T> {
        // Computes the formula that results by replacing each of the atoms
        // in `self` with that atom's image along `map`.
        match self {
            Formula::Atom(t) => map(t),
            Formula::Not(p) => Formula::not(&p.on_atoms(map)),
            Formula::And(p, q) => Formula::and(&p.on_atoms(map), &q.on_atoms(map)),
            Formula::Or(p, q) => Formula::or(&p.on_atoms(map), &q.on_atoms(map)),
            Formula::Imp(p, q) => Formula::imp(&p.on_atoms(map), &q.on_atoms(map)),
            Formula::Iff(p, q) => Formula::iff(&p.on_atoms(map), &q.on_atoms(map)),
            Formula::Forall(var, p) => Formula::forall(var, &p.on_atoms(map)),
            Formula::Exists(var, p) => Formula::exists(var, &p.on_atoms(map)),
            _ => self.clone(),
        }
    }

    pub fn over_atoms<Agg>(&self, combine: &dyn Fn(&T, Agg) -> Agg, aggregate: Agg) -> Agg {
        // Apply an aggregator `combine` across all atoms of `self`, keeping the result
        // in `aggregate`.
        match self {
            Formula::Atom(t) => combine(t, aggregate),
            Formula::Not(p) => p.over_atoms(combine, aggregate),
            Formula::And(p, q) | Formula::Or(p, q) | Formula::Imp(p, q) | Formula::Iff(p, q) => {
                p.over_atoms(combine, q.over_atoms(combine, aggregate))
            }
            Formula::Forall(_, p) | Formula::Exists(_, p) => p.over_atoms(combine, aggregate),
            _ => aggregate,
        }
    }

    pub fn atom_union<S: Clone + Hash + Eq>(&self, map: fn(&T) -> S) -> HashSet<S> {
        // The set of images (along `map`) of atoms in `self`.
        // Note that Harrison takes a map to an interable of S, but I think
        // this might be more natural?
        let combine: &dyn Fn(&T, Vec<S>) -> Vec<S> = &|t, mut agg| {
            let mut image: Vec<S> = vec![map(t)];
            image.append(&mut agg);
            image
        };
        let all = self.over_atoms(combine, vec![]);
        let iter = all.into_iter();
        HashSet::from_iter(iter)
    }

    pub fn atoms(&self) -> HashSet<T> {
        HashSet::from_iter(self.atom_union(|x| x.clone()))
    }

    pub fn negative(&self) -> bool {
        matches!(self, Formula::Not(_))
    }

    pub fn negate(&self) -> Formula<T> {
        match self {
            Formula::Not(p) => *p.clone(),
            _ => Formula::not(self),
        }
    }

    pub fn list_conj(items: &[Formula<T>]) -> Formula<T> {
        // The conjunction of all `items`.
        if items.is_empty() {
            Formula::True
        } else {
            items
                .iter()
                .cloned()
                .reduce(|x, y| Formula::and(&x, &y))
                .unwrap()
        }
    }

    pub fn list_disj(items: &[Formula<T>]) -> Formula<T> {
        // The disjunction of all `items`.
        if items.is_empty() {
            Formula::False
        } else {
            items
                .iter()
                .cloned()
                .reduce(|x, y| Formula::or(&x, &y))
                .unwrap()
        }
    }
}

#[cfg(test)]
mod formula_tests_general {
    use super::*;
    use crate::utils::slice_to_vec_of_owned;

    // We test with T = String.
    #[test]
    fn test_formula_equality_1() {
        let x: Formula<String> = Formula::<String>::False;
        let z: Formula<String> = Formula::<String>::False;
        assert_eq!(x, z);
    }

    #[test]
    fn test_formula_equality_2() {
        let x: Formula<String> = Formula::<String>::False;
        let z: Formula<String> = Formula::<String>::True;
        assert_ne!(x, z);
    }
    #[test]
    fn test_formula_equality_3() {
        let x: Formula<String> = Formula::iff(
            &Formula::atom(&String::from("hello")),
            &Formula::and(
                &Formula::atom(&String::from("apples")),
                &Formula::atom(&String::from("oranges")),
            ),
        );
        let y: Formula<String> = Formula::iff(
            &Formula::atom(&String::from("hello")),
            &Formula::and(
                &Formula::atom(&String::from("apples")),
                &Formula::atom(&String::from("oranges")),
            ),
        );
        assert_eq!(x, y);
    }
    #[test]
    fn test_formula_equality_4() {
        let x: Formula<String> = Formula::iff(
            &Formula::atom(&String::from("hello")),
            &Formula::and(
                &Formula::atom(&String::from("apples")),
                &Formula::atom(&String::from("bananas")),
            ),
        );
        let y: Formula<String> = Formula::iff(
            &Formula::atom(&String::from("hello")),
            &Formula::and(
                &Formula::atom(&String::from("apples")),
                &Formula::atom(&String::from("oranges")),
            ),
        );
        assert_ne!(x, y);
    }

    #[test]
    fn test_antecedent_and_consequent() {
        let ante = Formula::atom(&String::from("apples"));
        let cons = Formula::atom(&String::from("oranges"));
        let input: Formula<String> = Formula::imp(&ante, &cons);
        let result_ante = Formula::antecedent(&input);
        let result_cons = Formula::consequent(&input);
        assert_eq!(result_ante, ante);
        assert_eq!(result_cons, cons);
    }

    #[test]
    fn test_on_atoms() {
        let input: Formula<String> = Formula::or(
            &Formula::iff(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::forall("some_var", &Formula::atom(&String::from("C"))),
        );

        let foo = |s: &String| -> Formula<String> { Formula::atom(&(s.to_owned() + "X")) };

        let result = input.on_atoms(&foo);
        let desired: Formula<String> = Formula::or(
            &Formula::iff(
                &Formula::atom(&String::from("AX")),
                &Formula::atom(&String::from("BX")),
            ),
            &Formula::forall("some_var", &Formula::atom(&String::from("CX"))),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_over_atoms() {
        // We Let S = T = String.
        let input: Formula<String> = Formula::or(
            &Formula::iff(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::forall("some_var", &Formula::atom(&String::from("A"))),
        );

        // Some starting elements
        let agg_init = vec![String::from("C"), String::from("B")];
        // A simple aggregator that just appends
        let aggregator: &dyn Fn(&String, Vec<String>) -> Vec<String> = &|t, mut agg| {
            let mut image: Vec<String> = vec![t.clone()];
            image.append(&mut agg);
            image
        };

        let result = input.over_atoms(aggregator, agg_init);
        let desired = slice_to_vec_of_owned(&["A", "B", "A", "C", "B"]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_atom_union() {
        // We Let S = T = String.
        let input: Formula<String> = Formula::or(
            &Formula::iff(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::imp(
                &Formula::atom(&String::from("B")),
                &Formula::atom(&String::from("C")),
            ),
        );

        let foo = |s: &String| -> String { s.clone() + "X" };

        let result = input.atom_union(foo);
        let desired = HashSet::from_iter(slice_to_vec_of_owned(&["AX", "BX", "CX"]));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_negate() {
        let formula = Formula::atom(&"A".to_string());
        assert_eq!(
            formula.negate(),
            Formula::not(&Formula::atom(&"A".to_string()))
        );
        let formula = Formula::not(&Formula::atom(&"A".to_string()));
        assert_eq!(formula.negate(), Formula::atom(&"A".to_string()));
    }

    #[test]
    fn test_list_conj_list_disj() {
        let empty = vec![];
        let singleton = vec![Formula::Atom("A")];
        let multiple = vec![Formula::Atom("A"), Formula::Atom("B"), Formula::Atom("C")];

        assert_eq!(Formula::list_conj(&empty), Formula::<String>::True);
        assert_eq!(Formula::list_conj(&singleton), Formula::Atom("A"));
        assert_eq!(
            Formula::list_conj(&multiple),
            Formula::and(
                &Formula::and(&Formula::Atom("A"), &Formula::Atom("B")),
                &Formula::Atom("C")
            )
        );

        assert_eq!(Formula::list_disj(&empty), Formula::<String>::False);
        assert_eq!(Formula::list_disj(&singleton), Formula::Atom("A"));
        assert_eq!(
            Formula::list_disj(&multiple),
            Formula::or(
                &Formula::or(&Formula::Atom("A"), &Formula::Atom("B")),
                &Formula::Atom("C")
            )
        );
    }
}

// ### Formula Prettifying ###

impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    fn strip_quant(formula: &Formula<T>) -> (Vec<String>, Formula<T>) {
        // Remove all leading quantifiers and return tuple of quantified variables
        // and the stripped formula.
        let formula: Formula<T> = formula.clone();
        match formula {
            Formula::Forall(x, p) => {
                match *p {
                    Formula::Forall(_, _) => {
                        let (mut xs, q) = Formula::strip_quant(&p);
                        // NOTE: Order is reversed.
                        xs.push(x);
                        (xs, q)
                    }
                    _ => (vec![x], *p),
                }
            }

            Formula::Exists(x, p) => {
                match *p {
                    Formula::Exists(_, _) => {
                        let (mut xs, q) = Formula::strip_quant(&p);
                        // NOTE: Order is reversed.
                        xs.push(x);
                        (xs, q)
                    }
                    _ => (vec![x], *p),
                }
            }

            _ => (vec![], formula),
        }
    }

    fn maybe_bracketed(add_brackets: bool, middle: &str) -> String {
        let mut result = String::from("");
        if add_brackets {
            result.push('(');
        }
        result.push_str(middle);
        if add_brackets {
            result.push(')');
        }
        result
    }

    fn pretty_formula(
        atom_pretty: &dyn Fn(u32, &T) -> String,
        prec: u32,
        formula: &Formula<T>,
    ) -> String {
        /*NOTE: This is actually Harrison's *inner* print_formula with an additional pfn argument
         *
         * `prec` : operator precedence
         * `atom_pretty` : a subformatter taking a precedence and an atom (T). */

        match formula {
            Formula::False => String::from("false"),
            Formula::True => String::from("true"),
            Formula::Atom(t) => atom_pretty(prec, t),
            Formula::Not(p) => Formula::<T>::maybe_bracketed(
                prec > 10,
                &Formula::pretty_prefix(atom_pretty, 10, "~", p),
            ),
            Formula::And(p, q) => Formula::<T>::maybe_bracketed(
                prec > 8,
                &Formula::pretty_infix(atom_pretty, 8, "/\\", p, q),
            ),
            Formula::Or(p, q) => Formula::<T>::maybe_bracketed(
                prec > 6,
                &Formula::pretty_infix(atom_pretty, 6, "\\/", p, q),
            ),
            Formula::Imp(p, q) => Formula::<T>::maybe_bracketed(
                prec > 4,
                &Formula::pretty_infix(atom_pretty, 4, "==>", p, q),
            ),
            Formula::Iff(p, q) => Formula::<T>::maybe_bracketed(
                prec > 2,
                &Formula::pretty_infix(atom_pretty, 2, "<=>", p, q),
            ),
            Formula::Forall(_, _) => Formula::<T>::maybe_bracketed(
                prec > 0,
                &Formula::pretty_quant(atom_pretty, "forall", formula),
            ),
            Formula::Exists(_, _) => Formula::<T>::maybe_bracketed(
                prec > 0,
                &Formula::pretty_quant(atom_pretty, "exists", formula),
            ),
        }
    }

    fn pretty_quant(
        atom_pretty: &dyn Fn(u32, &T) -> String,
        qname: &str,
        formula: &Formula<T>,
    ) -> String {
        // Note that `formula` is the entire quantified formula (not just the body).
        let mut result = String::from("");

        let (mut vars, body) = Formula::strip_quant(formula);
        // `strip_quant` returns vars in reverse order.
        vars.reverse();
        result.push_str(qname);

        vars.iter().for_each(|v| {
            result.push(' ');
            result.push_str(v);
        });
        result.push_str(". ");

        result.push_str(&Formula::pretty_formula(atom_pretty, 9, &body));
        result
    }

    fn pretty_prefix(
        atom_pretty: &dyn Fn(u32, &T) -> String,
        prec: u32,
        symbol: &str,
        inner: &Formula<T>,
    ) -> String {
        let mut result = String::from(symbol);
        result.push_str(&Formula::pretty_formula(atom_pretty, prec, inner));
        result
    }

    fn pretty_infix(
        atom_pretty: &dyn Fn(u32, &T) -> String,
        prec: u32,
        symbol: &str,
        left: &Formula<T>,
        right: &Formula<T>,
    ) -> String {
        // As in the double negation case, this will lead to extra brackets in A & (B & C).
        let mut result = String::new();

        result.push_str(&Formula::pretty_formula(atom_pretty, prec + 1, left));
        result.push(' ');
        result.push_str(symbol);
        result.push(' ');
        result.push_str(&Formula::pretty_formula(atom_pretty, prec, right));
        result
    }

    pub fn pretty_general<P: Fn(u32, &T) -> String>(&self, atom_pretty: &P) -> String {
        // atom_pretty is a sub-prettifier for atoms (type T)
        // NOTE:  It appears that both times this is passed a `atom_pretty`, that function
        // ignores the precidence argument (u32).  Maybe simplify the type accordingly?
        Formula::pretty_formula(atom_pretty, 0, self)
    }
}

#[cfg(test)]
mod generic_ast_print_tests {
    // We let T = String for testing purposes.

    use super::*;

    #[test]
    fn test_maybe_bracket_no_indent() {
        let result1 = Formula::<String>::maybe_bracketed(true, "TESTING");
        let result2 = Formula::<String>::maybe_bracketed(false, "TESTING");
        assert_eq!(result1, "(TESTING)");
        assert_eq!(result2, "TESTING");
    }

    #[test]
    fn test_strip_quant() {
        let formula1 = Formula::atom(&String::from("Hello"));
        let result1 = Formula::strip_quant(&formula1);
        let desired1 = (vec![], formula1);
        assert_eq!(result1, desired1);

        let inner = Formula::atom(&String::from("Hello"));

        let formula2 = Formula::forall("var1", &inner);
        let result2 = Formula::strip_quant(&formula2);
        let desired2 = (vec![String::from("var1")], inner.clone());
        assert_eq!(result2, desired2);

        let formula3 = Formula::forall("var2", &Formula::forall("var1", &inner));
        let result3 = Formula::strip_quant(&formula3);
        let desired3 = (vec![String::from("var1"), String::from("var2")], inner);
        assert_eq!(result3, desired3);
    }

    fn _test_pprint_general(formula: Formula<String>, desired: &str) {
        let pfn = |_prec: u32, name: &String| {
            // A toy printer for `Atom<String>`s that simply prints the `String`.
            name.to_owned()
        };
        let result = formula.pretty_general(&pfn);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_pprint_general_single_atom() {
        let formula = Formula::atom(&String::from("Hello"));
        let desired = "Hello";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_simple_conjunction() {
        let formula = Formula::and(
            &Formula::atom(&String::from("Hello")),
            &Formula::atom(&String::from("Goodbye")),
        );
        let desired = "Hello /\\ Goodbye";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_or_in_and_left() {
        // Make sure that parens are printed.
        let formula = Formula::and(
            &Formula::or(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::atom(&String::from("C")),
        );
        let desired = "(A \\/ B) /\\ C";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_or_in_and_right() {
        // Make sure that parens are printed.
        let formula = Formula::and(
            &Formula::atom(&String::from("C")),
            &Formula::or(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
        );
        let desired = "C /\\ (A \\/ B)";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_or_left() {
        // Make sure that parens are not printed.
        let formula = Formula::or(
            &Formula::and(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::atom(&String::from("C")),
        );
        let desired = "A /\\ B \\/ C";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_or_right() {
        // Make sure that parens are not printed.
        let formula = Formula::or(
            &Formula::atom(&String::from("C")),
            &Formula::and(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
        );
        let desired = "C \\/ A /\\ B";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_and_left() {
        let formula = Formula::and(
            &Formula::and(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::atom(&String::from("C")),
        );
        let desired = "(A /\\ B) /\\ C";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_and_right() {
        let formula = Formula::and(
            &Formula::atom(&String::from("C")),
            &Formula::and(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
        );
        let desired = "C /\\ A /\\ B";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_simple_quantified() {
        let formula = Formula::forall("x", &Formula::atom(&String::from("Hello")));
        let desired = "forall x. Hello";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_quantified_conjunction() {
        let formula = Formula::forall(
            "x",
            &Formula::and(
                &Formula::atom(&String::from("Hello")),
                &Formula::atom(&String::from("Goodbye")),
            ),
        );
        let desired = "forall x. (Hello /\\ Goodbye)";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_quantified_multivar() {
        let formula = Formula::forall(
            "var1",
            &Formula::forall("var2", &Formula::atom(&String::from("Hello"))),
        );
        let desired = "forall var1 var2. Hello";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_quantified_in_binary() {
        let formula = Formula::iff(
            &Formula::atom(&String::from("Goodbye")),
            &Formula::forall("var1", &Formula::atom(&String::from("Hello"))),
        );
        let desired = "Goodbye <=> (forall var1. Hello)";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_negate_atom() {
        let formula = Formula::not(&Formula::atom(&"Hello".to_string()));
        let desired = "~Hello";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_double_negation() {
        let formula = Formula::not(&Formula::not(&Formula::atom(&"Hello".to_string())));
        let desired = "~~Hello";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_negate_quantified() {
        let formula = Formula::not(&Formula::forall(
            "x",
            &Formula::atom(&String::from("Hello")),
        ));
        let desired = "~(forall x. Hello)";
        _test_pprint_general(formula, desired);
    }
}

// Eval and simplification funtionality.
impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    pub fn eval_core<
        AtomEval: Fn(&T) -> bool,
        ForallEval: Fn(&str, &Formula<T>) -> bool,
        ExistsEval: Fn(&str, &Formula<T>) -> bool,
    >(
        &self,
        atom_eval: &AtomEval,
        forall_eval: &ForallEval,
        exists_eval: &ExistsEval,
    ) -> bool {
        match self {
            Formula::True => true,
            Formula::False => false,
            Formula::Atom(t) => atom_eval(t),
            Formula::Not(p) => !p.eval_core(atom_eval, forall_eval, exists_eval),
            Formula::And(p, q) => {
                p.eval_core(atom_eval, forall_eval, exists_eval)
                    && q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Or(p, q) => {
                p.eval_core(atom_eval, forall_eval, exists_eval)
                    || q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Imp(p, q) => {
                !p.eval_core(atom_eval, forall_eval, exists_eval)
                    || q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Iff(p, q) => {
                p.eval_core(atom_eval, forall_eval, exists_eval)
                    == q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Forall(var, p) => forall_eval(var, p),
            Formula::Exists(var, p) => exists_eval(var, p),
        }
    }

    pub fn psimplify_step(formula: &Formula<T>) -> Formula<T> {
        // Simplify formulas involving `True` or `False` (constants).  Also
        // eliminate double negations

        match formula {
            Formula::Not(r) => match *r.clone() {
                Formula::False => Formula::True,
                Formula::True => Formula::False,
                Formula::Not(p) => *p.clone(),
                _ => formula.clone(),
            },

            Formula::And(r, s) => match (*r.clone(), *s.clone()) {
                (p, Formula::True) | (Formula::True, p) => p.clone(),
                (_, Formula::False) | (Formula::False, _) => Formula::False,
                _ => formula.clone(),
            },

            Formula::Or(r, s) => match (*r.clone(), *s.clone()) {
                (_, Formula::True) | (Formula::True, _) => Formula::True,
                (p, Formula::False) | (Formula::False, p) => p.clone(),
                _ => formula.clone(),
            },

            Formula::Imp(r, s) => match (*r.clone(), *s.clone()) {
                (_, Formula::True) | (Formula::False, _) => Formula::True,
                (Formula::True, Formula::False) => Formula::False,
                (p, Formula::False) => Formula::not(&p),
                (Formula::True, p) => p.clone(),
                _ => formula.clone(),
            },
            Formula::Iff(r, s) => match (*r.clone(), *s.clone()) {
                (Formula::True, Formula::True) | (Formula::False, Formula::False) => Formula::True,
                (Formula::True, Formula::False) | (Formula::False, Formula::True) => Formula::False,

                (Formula::True, p) | (p, Formula::True) => p.clone(),
                (Formula::False, p) | (p, Formula::False) => Formula::not(&p),
                _ => formula.clone(),
            },

            // The following two arms are not in Harrison
            _ => formula.clone(),
        }
    }

    pub fn simplify_recursive(&self, step: &dyn Fn(&Formula<T>) -> Formula<T>) -> Formula<T> {
        // Apply `psimplify1` bottom-up to `self`.
        match self {
            Formula::Not(p) => step(&Formula::not(&p.simplify_recursive(step))),
            Formula::And(p, q) => step(&Formula::and(
                &p.simplify_recursive(step),
                &q.simplify_recursive(step),
            )),
            Formula::Or(p, q) => step(&Formula::or(
                &p.simplify_recursive(step),
                &q.simplify_recursive(step),
            )),
            Formula::Imp(p, q) => step(&Formula::imp(
                &p.simplify_recursive(step),
                &q.simplify_recursive(step),
            )),
            Formula::Iff(p, q) => step(&Formula::iff(
                &p.simplify_recursive(step),
                &q.simplify_recursive(step),
            )),
            Formula::Forall(x, p) => step(&Formula::forall(x, &p.simplify_recursive(step))),
            Formula::Exists(y, p) => step(&Formula::exists(y, &p.simplify_recursive(step))),
            _ => self.clone(),
        }
    }
}

#[cfg(test)]
mod formula_tests_simplify_and_eval {
    use super::*;

    #[test]
    fn test_psimplify_step() {
        let formula = Formula::not(&Formula::not(&Formula::not(&Formula::atom(&String::from(
            "Hello",
        )))));
        let result = Formula::not(&Formula::atom(&String::from("Hello")));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::not(&Formula::<String>::True);
        let result = Formula::False;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::not(&Formula::<String>::False);
        let result = Formula::True;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::and(&Formula::True, &Formula::atom(&String::from("A")));
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::and(&Formula::atom(&String::from("A")), &Formula::True);
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::and(&Formula::False, &Formula::atom(&String::from("A")));
        let result = Formula::False;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::and(&Formula::atom(&String::from("A")), &Formula::False);
        let result = Formula::False;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::or(&Formula::True, &Formula::atom(&String::from("A")));
        let result = Formula::True;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::or(&Formula::atom(&String::from("A")), &Formula::True);
        let result = Formula::True;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::or(&Formula::False, &Formula::atom(&String::from("A")));
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::or(&Formula::atom(&String::from("A")), &Formula::False);
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::imp(&Formula::True, &Formula::atom(&String::from("A")));
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::imp(&Formula::atom(&String::from("A")), &Formula::True);
        let result = Formula::True;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::imp(&Formula::False, &Formula::atom(&String::from("A")));
        let result = Formula::True;
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::imp(&Formula::atom(&String::from("A")), &Formula::False);
        let result = Formula::not(&Formula::atom(&String::from("A")));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::iff(&Formula::True, &Formula::atom(&String::from("A")));
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::iff(&Formula::atom(&String::from("A")), &Formula::True);
        let result = Formula::atom(&String::from("A"));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::iff(&Formula::False, &Formula::atom(&String::from("A")));
        let result = Formula::not(&Formula::atom(&String::from("A")));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::iff(&Formula::atom(&String::from("A")), &Formula::False);
        let result = Formula::not(&Formula::atom(&String::from("A")));
        assert_eq!(Formula::psimplify_step(&formula), result);

        let formula = Formula::iff(&Formula::<String>::False, &Formula::False);
        let result = Formula::True;
        assert_eq!(Formula::psimplify_step(&formula), result);
    }

    #[test]
    fn test_simplify_recursive() {
        let step = &Formula::psimplify_step;

        let formula = Formula::or(
            &Formula::and(&Formula::False, &Formula::False),
            &Formula::imp(&Formula::False, &Formula::atom(&"B".to_string())),
        );
        let result = Formula::True;
        assert_eq!(formula.simplify_recursive(step), result);

        let formula = Formula::forall(
            "x",
            &Formula::imp(
                &Formula::imp(
                    &Formula::True,
                    &Formula::iff(&Formula::atom(&"x".to_string()), &Formula::False),
                ),
                &Formula::exists(
                    "y",
                    &Formula::not(&Formula::or(
                        &Formula::atom(&"y".to_string()),
                        &Formula::and(&Formula::False, &Formula::atom(&"z".to_string())),
                    )),
                ),
            ),
        );
        let result = Formula::forall(
            "x",
            &Formula::imp(
                &Formula::not(&Formula::atom(&String::from("x"))),
                &Formula::exists("y", &Formula::not(&Formula::atom(&String::from("y")))),
            ),
        );

        assert_eq!(formula.simplify_recursive(step), result);
    }
    #[test]
    fn test_eval_core() {
        let mut formula;

        fn empty(_: &String) -> bool {
            panic!("Did not expect to find atoms.");
        }
        fn qempty(_: &str, _: &Formula<String>) -> bool {
            panic!("Did not expect to find quantifiers.");
        }

        formula = Formula::True;
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::False;
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::not(&Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::not(&Formula::True);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(&Formula::True, &Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(&Formula::False, &Formula::True);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(&Formula::True, &Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(&Formula::False, &Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(&Formula::True, &Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(&Formula::False, &Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(&Formula::True, &Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(&Formula::False, &Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(&Formula::True, &Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(&Formula::False, &Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(&Formula::True, &Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(&Formula::False, &Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(&Formula::True, &Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(&Formula::False, &Formula::True);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(&Formula::True, &Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(&Formula::False, &Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        fn atom_eval(x: &String) -> bool {
            match x {
                x if x == "A" => true,
                x if x == "B" => false,
                x if x == "C" => true,
                _ => false,
            }
        }

        fn quantifier_eval(_var: &str, sub: &Formula<String>) -> bool {
            // Ignore quantifiers, and just eval quantified formula.
            sub.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval)
        }

        formula = Formula::atom(&"A".to_string());
        assert!(formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval));

        formula = Formula::atom(&"B".to_string());
        assert!(!formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval));

        formula = Formula::iff(
            &Formula::atom(&"C".to_string()),
            &Formula::and(
                &Formula::atom(&"A".to_string()),
                &Formula::atom(&"B".to_string()),
            ),
        );
        assert!(!formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval));

        // Should be equivalent to just And(B, C) since quantifier sub-eval ignores quantifiers.
        formula = Formula::exists(
            "X",
            &Formula::and(
                &Formula::atom(&"B".to_string()),
                &Formula::forall("Y", &Formula::atom(&"C".to_string())),
            ),
        );
        assert!(!formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval),)
    }
}

// ##### Normal Forms #####

// NNF
impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    pub fn raw_nnf(&self) -> Formula<T> {
        // Negation normal form

        match self {
            Formula::And(p, q) => Formula::and(&p.raw_nnf(), &q.raw_nnf()),
            Formula::Or(p, q) => Formula::or(&p.raw_nnf(), &q.raw_nnf()),
            Formula::Imp(p, q) => Formula::or(&Formula::not(p).raw_nnf(), &q.raw_nnf()),
            Formula::Iff(p, q) => Formula::or(
                &Formula::and(&p.raw_nnf(), &q.raw_nnf()),
                &Formula::and(&Formula::not(q).raw_nnf(), &Formula::not(p).raw_nnf()),
            ),
            Formula::Not(r) => match *r.clone() {
                Formula::Not(p) => p.raw_nnf(),
                Formula::And(p, q) => {
                    Formula::or(&Formula::not(&p).raw_nnf(), &Formula::not(&q).raw_nnf())
                }
                Formula::Or(p, q) => {
                    Formula::and(&Formula::not(&p).raw_nnf(), &Formula::not(&q).raw_nnf())
                }
                Formula::Imp(p, q) => Formula::and(&p.raw_nnf(), &Formula::not(&q).raw_nnf()),
                Formula::Iff(p, q) => Formula::or(
                    &Formula::and(&p.raw_nnf(), &Formula::not(&q).raw_nnf()),
                    &Formula::and(&Formula::not(&p).raw_nnf(), &q.raw_nnf()),
                ),
                Formula::Forall(x, p) => Formula::exists(&x, &Formula::not(&p).raw_nnf()),
                Formula::Exists(x, p) => Formula::forall(&x, &Formula::not(&p).raw_nnf()),
                _ => self.clone(),
            },
            Formula::Forall(x, p) => Formula::forall(x, &p.raw_nnf()),
            Formula::Exists(x, p) => Formula::exists(x, &p.raw_nnf()),
            _ => self.clone(),
        }
    }

    pub fn raw_nenf(&self) -> Formula<T> {
        // Negation normal form also allowing equivalences (iff).
        // NOTE that this and `raw_nnf` could factor through a common function
        match self {
            Formula::And(p, q) => Formula::and(&p.raw_nenf(), &q.raw_nenf()),
            Formula::Or(p, q) => Formula::or(&p.raw_nenf(), &q.raw_nenf()),
            Formula::Imp(p, q) => Formula::or(&Formula::not(p).raw_nenf(), &q.raw_nenf()),
            Formula::Iff(p, q) => Formula::iff(&p.raw_nenf(), &q.raw_nenf()),
            Formula::Not(r) => match *r.clone() {
                Formula::Not(p) => p.raw_nenf(),
                Formula::And(p, q) => {
                    Formula::or(&Formula::not(&p).raw_nenf(), &Formula::not(&q).raw_nenf())
                }
                Formula::Or(p, q) => {
                    Formula::and(&Formula::not(&p).raw_nenf(), &Formula::not(&q).raw_nenf())
                }
                Formula::Imp(p, q) => Formula::and(&p.raw_nenf(), &Formula::not(&q).raw_nenf()),
                Formula::Iff(p, q) => Formula::iff(&p.raw_nenf(), &Formula::not(&q).raw_nenf()),
                Formula::Forall(x, p) => Formula::exists(&x, &Formula::not(&p).raw_nenf()),
                Formula::Exists(x, p) => Formula::forall(&x, &Formula::not(&p).raw_nenf()),
                _ => self.clone(),
            },

            Formula::Forall(x, p) => Formula::forall(x, &p.raw_nenf()),
            Formula::Exists(x, p) => Formula::exists(x, &p.raw_nenf()),

            _ => self.clone(),
        }
    }
}

// Representation of literal to be used with FormulaSet.
// Since we don't want to allow any other type of Formula
// in FormulaSet clauses.
// Pos corresponds to an atom, and Neg to a negated atom.
#[derive(Debug, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum FSLiteral<T> {
    Pos(T),
    Neg(T),
}

impl<T: Debug + Clone + Hash + Eq + Ord> FSLiteral<T> {
    pub fn is_neg(&self) -> bool {
        matches!(self, FSLiteral::Neg(_))
    }

    fn is_pos(&self) -> bool {
        // NOTE: that the way _negative and _positive are defined,
        // every non-literal will count as `_positive`.
        !self.is_neg()
    }

    pub fn negate(&self) -> FSLiteral<T> {
        match self {
            FSLiteral::Neg(p) => FSLiteral::Pos(p.to_owned()),
            FSLiteral::Pos(p) => FSLiteral::Neg(p.to_owned()),
        }
    }

    pub fn to_formula(&self) -> Formula<T> {
        match self {
            FSLiteral::Pos(p) => Formula::atom(p),
            FSLiteral::Neg(p) => Formula::not(&Formula::atom(p)),
        }
    }

    pub fn list_conj(items: &[FSLiteral<T>]) -> Formula<T> {
        // The conjunction of all `items`.
        if items.is_empty() {
            Formula::True
        } else {
            items
                .iter()
                .map(|lit| lit.to_formula())
                .reduce(|x, y| Formula::and(&x, &y))
                .unwrap()
        }
    }

    pub fn list_disj(items: &[FSLiteral<T>]) -> Formula<T> {
        // The conjunction of all `items`.
        if items.is_empty() {
            Formula::False
        } else {
            items
                .iter()
                .map(|lit| lit.to_formula())
                .reduce(|x, y| Formula::or(&x, &y))
                .unwrap()
        }
    }
}

// `FormulaSet`: a set representations of Formulas in disjunctive or conjunctive normal form
// (we need to specify which in order to have a unique meaning)..
// The inner sets are the clauses, and the outer set represents their disjunction
// (for DNF) for conjunction (for CNF).
// We use BTreeSet here so that we can rely on an ordering
// for tests.
pub type Clause<T> = BTreeSet<FSLiteral<T>>;

// Although under the hood these are the same, it is crucial to be explicit about what
// representation of a formula they are assuming.
pub type AbstractFormulaSet<T> = BTreeSet<Clause<T>>;
pub type CNFFormulaSet<T> = BTreeSet<Clause<T>>;
pub type DNFFormulaSet<T> = BTreeSet<Clause<T>>;

impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    pub fn set_distrib_and_over_or(
        formula1: &DNFFormulaSet<T>,
        formula2: &DNFFormulaSet<T>,
    ) -> DNFFormulaSet<T> {
        let mut result = DNFFormulaSet::new();
        for conj1 in formula1 {
            for conj2 in formula2 {
                result.insert(conj1 | conj2);
            }
        }
        result
    }

    fn purednf(&self) -> DNFFormulaSet<T> {
        // DNF by converting formulas to set of sets representation.
        let simplified = self.simplify_recursive(&Formula::psimplify_step);
        let nnf = simplified.raw_nnf();

        match nnf {
            Formula::False => DNFFormulaSet::new(),
            Formula::True => BTreeSet::from([BTreeSet::new()]),
            Formula::Atom(t) => BTreeSet::from([BTreeSet::from([FSLiteral::Pos(t)])]),
            Formula::Not(t) => {
                if let Formula::Atom(s) = *t {
                    BTreeSet::from([BTreeSet::from([FSLiteral::Neg(s)])])
                } else {
                    panic!("Only atoms should be negated in nnf")
                }
            }
            Formula::And(p, q) => Formula::set_distrib_and_over_or(&p.purednf(), &q.purednf()),
            Formula::Or(p, q) => &p.purednf() | &q.purednf(),
            _ => panic!("Unrecognized formula type {nnf:?} for _puredfn."),
        }
    }

    fn purecnf(&self) -> CNFFormulaSet<T> {
        // CNF by converting formulas to set of sets representation.
        let negation_in_purednf: CNFFormulaSet<T> = Formula::not(self).purednf();
        // distribute matching negation from outside (and assuming dual representation).
        let result: CNFFormulaSet<T> = negation_in_purednf
            .iter()
            .map(|conjunction| conjunction.iter().map(|lit| lit.negate()).collect())
            .collect();
        result
    }

    fn contradictory_lits(clause: &Clause<T>) -> bool {
        // Whether `lits` contains two literals of the form `p` and `~p`.
        let pos: HashSet<FSLiteral<T>> = clause.iter().filter(|x| x.is_pos()).cloned().collect();

        let neg: HashSet<FSLiteral<T>> = clause
            .iter()
            .filter(|x| x.is_neg())
            .map(|lit| lit.negate())
            .collect();

        pos.intersection(&neg).count() != 0
    }

    fn strip_supersets(formula: &CNFFormulaSet<T>) -> CNFFormulaSet<T> {
        // Remove all inner sets that contain other inner sets.
        let mut result = CNFFormulaSet::new();
        for conj1 in formula {
            let mut keep = true;
            for conj2 in formula {
                if conj2 == conj1 {
                    continue;
                } else if conj1.is_superset(conj2) {
                    // This must be proper containment.
                    keep = false;
                    break;
                }
            }
            if keep {
                result.insert(conj1.clone());
            }
        }
        result
    }

    pub fn strip_contradictory(formula_set: &AbstractFormulaSet<T>) -> AbstractFormulaSet<T> {
        // If a either type of FormulaSet has has contradictory lits, the clause should be removed.
        // since it's either False /\\ ... (for DNF) or True \\/ ... (for CNF).
        formula_set
            .iter()
            .filter(|x| !Formula::contradictory_lits(x))
            .cloned()
            .collect()
    }

    pub fn formulaset_to_dnf_formula(formula_set: DNFFormulaSet<T>) -> Formula<T> {
        // Interprets the formula set a
        let partial: Vec<Formula<T>> = formula_set
            .into_iter()
            .map(Vec::from_iter)
            .map(|conj| FSLiteral::list_conj(&conj))
            .collect();
        Formula::list_disj(&partial)
    }

    pub fn formulaset_to_cnf_formula(formula_set: CNFFormulaSet<T>) -> Formula<T> {
        let partial: Vec<Formula<T>> = formula_set
            .into_iter()
            .map(Vec::from_iter)
            .map(|disj| FSLiteral::list_disj(&disj))
            .collect();
        Formula::list_conj(&partial)
    }

    fn is_disjunction_of_literals(&self) -> bool {
        match self {
            Formula::Atom(_) => true,
            Formula::Not(p) if matches!(**p, Formula::Atom(_)) => true,
            Formula::Or(p, q) => p.is_disjunction_of_literals() && q.is_disjunction_of_literals(),
            _ => false,
        }
    }

    pub fn is_cnf(&self) -> bool {
        // The one-clause case.
        if Formula::is_disjunction_of_literals(self) {
            return true;
        }
        match self {
            Formula::And(p, q) => p.is_cnf() && q.is_cnf(),
            _ => false,
        }
    }

    pub fn to_dnf_formulaset(&self) -> DNFFormulaSet<T> {
        // Note that a formula is a non-satisfiable iff this function returns Formula::False
        // (the empty disjunction).
        let formula_set = self.purednf();
        Formula::strip_contradictory(&Formula::strip_supersets(&formula_set))
    }

    pub fn to_cnf_formulaset(&self) -> CNFFormulaSet<T> {
        // Note that a formula is a tautology iff this function returns Formula::True
        // (the empty conjunction)
        let formula_set = self.purecnf();
        Formula::strip_contradictory(&Formula::strip_supersets(&formula_set))
    }

    pub fn to_cnf(&self) -> Formula<T> {
        // Note that a formula is a tautology iff this function returns Formula::True
        // (the empty conjunction)
        let formula_set = self.to_cnf_formulaset();
        Formula::formulaset_to_cnf_formula(formula_set)
    }

    pub fn to_dnf(&self) -> Formula<T> {
        // Note that a formula is a non-satisfiable iff this function returns Formula::False
        // (the empty disjunction).
        let formula_set = self.to_dnf_formulaset();
        Formula::formulaset_to_dnf_formula(formula_set)
    }
}

#[cfg(test)]
mod nnf_tests {
    use super::*;

    #[test]
    fn test_raw_nnf() {
        let formula = Formula::not(&Formula::and(
            &Formula::atom(&"A".to_string()),
            &Formula::or(
                &Formula::atom(&"B".to_string()),
                &Formula::atom(&"C".to_string()),
            ),
        ));

        let desired = Formula::or(
            &Formula::not(&Formula::atom(&"A".to_string())),
            &Formula::and(
                &Formula::not(&Formula::atom(&"B".to_string())),
                &Formula::not(&Formula::atom(&"C".to_string())),
            ),
        );
        assert_eq!(formula.raw_nnf(), desired);

        let formula = Formula::exists(
            "z",
            &Formula::not(&Formula::imp(
                &Formula::not(&Formula::forall("A", &Formula::atom(&"A".to_string()))),
                &Formula::iff(
                    &Formula::atom(&"B".to_string()),
                    &Formula::atom(&"C".to_string()),
                ),
            )),
        );
        let desired = Formula::exists(
            "z",
            &Formula::and(
                &Formula::exists("A", &Formula::not(&Formula::atom(&("A".to_string())))),
                &Formula::or(
                    &Formula::and(
                        &Formula::atom(&"B".to_string()),
                        &Formula::not(&Formula::atom(&"C".to_string())),
                    ),
                    &Formula::and(
                        &Formula::not(&Formula::atom(&"B".to_string())),
                        &Formula::atom(&"C".to_string()),
                    ),
                ),
            ),
        );
        assert_eq!(formula.raw_nnf(), desired);
    }

    #[test]
    fn test_raw_nenf() {
        let formula = Formula::not(&Formula::and(
            &Formula::atom(&"A".to_string()),
            &Formula::or(
                &Formula::atom(&"B".to_string()),
                &Formula::atom(&"C".to_string()),
            ),
        ));
        let desired = Formula::or(
            &Formula::not(&Formula::atom(&"A".to_string())),
            &Formula::and(
                &Formula::not(&Formula::atom(&"B".to_string())),
                &Formula::not(&Formula::atom(&"C".to_string())),
            ),
        );
        assert_eq!(formula.raw_nenf(), desired);
        let formula = Formula::exists(
            "z",
            &Formula::not(&Formula::imp(
                &Formula::not(&Formula::forall("A", &Formula::atom(&"A".to_string()))),
                &Formula::iff(
                    &Formula::atom(&"B".to_string()),
                    &Formula::atom(&"C".to_string()),
                ),
            )),
        );
        let desired = Formula::exists(
            "z",
            &Formula::and(
                &Formula::exists("A", &Formula::not(&Formula::atom(&"A".to_string()))),
                &Formula::iff(
                    &Formula::atom(&"B".to_string()),
                    &Formula::not(&Formula::atom(&"C".to_string())),
                ),
            ),
        );
        assert_eq!(formula.raw_nenf(), desired);
    }
}

#[cfg(test)]
mod formula_set_test {
    use super::*;

    #[test]
    fn test_set_distrib_and_over_or() {
        let formula1 = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("B")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let formula2 = BTreeSet::from([
            BTreeSet::from([FSLiteral::Pos(String::from("A"))]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);

        let desired = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("B")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("A")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("D")),
            ]),
        ]);
        let result = Formula::set_distrib_and_over_or(&formula1, &formula2);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_purednf() {
        let formula = Formula::or(
            &Formula::False,
            &Formula::and(
                &Formula::or(
                    &Formula::and(&Formula::atom(&String::from("A")), &Formula::True),
                    &Formula::and(
                        &Formula::atom(&String::from("B")),
                        &Formula::atom(&String::from("C")),
                    ),
                ),
                &Formula::or(
                    &Formula::atom(&String::from("A")),
                    &Formula::and(
                        &Formula::atom(&String::from("D")),
                        &Formula::atom(&String::from("C")),
                    ),
                ),
            ),
        );

        let result = formula.purednf();
        let desired = BTreeSet::from([
            BTreeSet::from([FSLiteral::Pos(String::from("A"))]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("A")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("D")),
            ]),
        ]);
        assert_eq!(result, desired);

        // Trivial:
        let result_true = Formula::<String>::True.purednf();
        let result_false = Formula::<String>::False.purednf();
        assert_eq!(result_true, BTreeSet::from([BTreeSet::from([])]));
        assert_eq!(result_false, BTreeSet::from([]));
    }

    #[test]
    fn test_purecnf() {
        let formula = Formula::and(
            &Formula::or(
                &Formula::and(
                    &Formula::atom(&String::from("A")),
                    &Formula::or(&Formula::True, &Formula::atom(&String::from("E"))),
                ),
                &Formula::and(
                    &Formula::atom(&String::from("B")),
                    &Formula::atom(&String::from("C")),
                ),
            ),
            &Formula::or(
                &Formula::or(
                    &Formula::not(&Formula::atom(&String::from("A"))),
                    &Formula::and(&Formula::False, &Formula::atom(&String::from("F"))),
                ),
                &Formula::and(
                    &Formula::atom(&String::from("D")),
                    &Formula::atom(&String::from("C")),
                ),
            ),
        );

        let desired = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("B")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        assert_eq!(formula.purecnf(), desired);

        let result_true = (Formula::<String>::True).purecnf();
        let result_false = (Formula::<String>::False).purecnf();
        assert_eq!(result_false, BTreeSet::from([BTreeSet::from([])]));
        assert_eq!(result_true, BTreeSet::from([]));
    }
    #[test]
    fn test_contradictory_lits() {
        let lits1 = BTreeSet::from([
            FSLiteral::Pos(String::from("A")),
            FSLiteral::Pos(String::from("B")),
        ]);
        let lits2 = BTreeSet::from([
            FSLiteral::Pos(String::from("A")),
            FSLiteral::Pos(String::from("B")),
            FSLiteral::Neg(String::from("A")),
        ]);

        assert!(!Formula::contradictory_lits(&lits1));
        assert!(Formula::contradictory_lits(&lits2));
    }

    #[test]
    fn test_strip_supersets() {
        let formula = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("A")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("E")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("E")),
            ]),
        ]);

        let desired = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("A")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
                FSLiteral::Pos(String::from("E")),
            ]),
        ]);
        let result = Formula::strip_supersets(&formula);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dnf() {
        let formula = Formula::and(
            &Formula::or(
                &Formula::and(&Formula::atom(&String::from("A")), &Formula::True),
                &Formula::and(
                    &Formula::atom(&String::from("B")),
                    &Formula::not(&Formula::atom(&String::from("B"))),
                ),
            ),
            &Formula::or(
                &Formula::atom(&String::from("B")),
                &Formula::and(
                    &Formula::atom(&String::from("D")),
                    &Formula::atom(&String::from("C")),
                ),
            ),
        );
        let result = formula.to_dnf();
        let desired = Formula::or(
            &Formula::and(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("B")),
            ),
            &Formula::and(
                &Formula::and(
                    &Formula::atom(&String::from("A")),
                    &Formula::atom(&String::from("C")),
                ),
                &Formula::atom(&String::from("D")),
            ),
        );

        assert_eq!(result, desired);
    }

    #[test]
    fn test_dnf_unsatisfiable() {
        // Should be False on contradictions.
        let formula = Formula::and(
            &Formula::atom(&String::from("P")),
            &Formula::not(&Formula::atom(&String::from("P"))),
        );

        assert_eq!(formula.to_dnf(), Formula::False);
    }

    #[test]
    fn test_cnf_tautology() {
        // Should be True on tautologies.
        let formula = Formula::or(
            &Formula::atom(&String::from("P")),
            &Formula::not(&Formula::atom(&String::from("P"))),
        );
        assert_eq!(formula.to_cnf(), Formula::True);
    }

    #[test]
    fn test_cnf() {
        let formula = Formula::and(
            &Formula::or(
                &Formula::and(
                    &Formula::atom(&String::from("A")),
                    &Formula::or(&Formula::True, &Formula::atom(&String::from("E"))),
                ),
                &Formula::and(
                    &Formula::atom(&String::from("B")),
                    &Formula::atom(&String::from("C")),
                ),
            ),
            &Formula::or(
                &Formula::or(
                    &Formula::not(&Formula::atom(&String::from("A"))),
                    &Formula::and(&Formula::False, &Formula::atom(&String::from("F"))),
                ),
                &Formula::and(
                    &Formula::atom(&String::from("D")),
                    &Formula::atom(&String::from("C")),
                ),
            ),
        );

        let desired = Formula::and(
            &Formula::and(
                &Formula::and(
                    &Formula::or(
                        &Formula::atom(&String::from("A")),
                        &Formula::atom(&String::from("B")),
                    ),
                    &Formula::or(
                        &Formula::atom(&String::from("A")),
                        &Formula::atom(&String::from("C")),
                    ),
                ),
                &Formula::or(
                    &Formula::atom(&String::from("C")),
                    &Formula::not(&Formula::atom(&String::from("A"))),
                ),
            ),
            &Formula::or(
                &Formula::atom(&String::from("D")),
                &Formula::not(&Formula::atom(&String::from("A"))),
            ),
        );
        assert_eq!(formula.to_cnf(), desired);
    }

    #[test]
    fn test_is_cnf() {
        let formula = Formula::and(
            &Formula::not(&Formula::atom(&String::from("A"))),
            &Formula::atom(&String::from("B")),
        );
        assert!(formula.is_cnf());
        let formula = Formula::or(
            &Formula::not(&Formula::atom(&String::from("A"))),
            &Formula::atom(&String::from("B")),
        );
        assert!(formula.is_cnf());
        let formula = Formula::or(
            &Formula::and(
                &Formula::atom(&String::from("A")),
                &Formula::atom(&String::from("C")),
            ),
            &Formula::atom(&String::from("B")),
        );
        assert!(!formula.is_cnf());
        let formula = Formula::and(
            &Formula::or(
                &Formula::or(
                    &Formula::atom(&String::from("D")),
                    &Formula::atom(&String::from("A")),
                ),
                &Formula::atom(&String::from("C")),
            ),
            &Formula::atom(&String::from("B")),
        );
        assert!(formula.is_cnf());
    }
}

pub type ErrInner = &'static str;

// SAT
//
// ### Davis-Putnam (DP)
impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    fn _one_literal_rule(clauses: &CNFFormulaSet<T>) -> Result<CNFFormulaSet<T>, ErrInner> {
        // If there is a singleton clause (containing one literal) then the only
        // satisfying interpretations are those where that literal is true.
        // Thus we can remove all clauses that contain that literal (they will be true)
        // and we can remove the negation of that literal from all clauses that contain
        // that negation (that disjunct cannot be true).
        for clause in clauses {
            if clause.len() == 1 {
                let clause_vec: Vec<FSLiteral<T>> = Vec::from_iter(clause.clone());
                let literal = clause_vec[0].clone();
                let negation = literal.negate();
                let result: CNFFormulaSet<T> = clauses
                    .iter()
                    .filter(|clause| !clause.contains(&literal))
                    .cloned()
                    .collect();
                let result: CNFFormulaSet<T> = result
                    .iter()
                    .map(|clause| {
                        clause
                            .difference(&BTreeSet::from([negation.clone()]))
                            .cloned()
                            .collect()
                    })
                    .collect();
                return Ok(result);
            }
        }
        Err("No unit clauses found.")
    }

    fn _affirmative_negative_rule(
        clauses: &CNFFormulaSet<T>,
    ) -> Result<CNFFormulaSet<T>, ErrInner> {
        // Remove all clauses that contain literals that occur either all positively or
        // all negatively.
        let all_literals: BTreeSet<FSLiteral<T>> =
            clauses.iter().fold(BTreeSet::new(), |x, y| &x | y);
        let (negative, positive): (Clause<T>, Clause<T>) =
            all_literals.into_iter().partition(FSLiteral::is_neg);
        // The atoms whose negations appear in a clause.
        let unnegated: BTreeSet<FSLiteral<T>> = negative
            .into_iter()
            .map(|neg| FSLiteral::negate(&neg))
            .collect();
        let positive_only: BTreeSet<FSLiteral<T>> =
            positive.difference(&unnegated).cloned().collect();
        let negative_only: BTreeSet<FSLiteral<T>> =
            unnegated.difference(&positive).cloned().collect();
        let renegated: BTreeSet<FSLiteral<T>> = negative_only
            .into_iter()
            .map(|neg| FSLiteral::negate(&neg))
            .collect();
        let pure: BTreeSet<FSLiteral<T>> = &positive_only | &renegated;

        if pure.is_empty() {
            Err("No strictly positively or strictly negatively occurring literals.")
        } else {
            let value: CNFFormulaSet<T> = clauses
                .iter()
                .filter(|clause| {
                    clause
                        .intersection(&pure)
                        .collect::<BTreeSet<_>>()
                        .is_empty()
                })
                .cloned()
                .collect();
            Ok(value)
        }
    }

    // For _resolution_rule (DP only).
    fn resolve_atom(clauses: &CNFFormulaSet<T>, literal: &FSLiteral<T>) -> CNFFormulaSet<T> {
        // Given a `literal` p appearing both positively in some clauses p V C_i
        // and negatively in others ~p V D_j, remove all such clauses and replace them with
        // all possible C_i V D_j.
        let clauses = Formula::strip_contradictory(clauses);
        let (contains_literal, doesnt_contain_literal): (CNFFormulaSet<T>, CNFFormulaSet<T>) =
            clauses
                .into_iter()
                .partition(|clause| clause.contains(literal));
        let negated = &FSLiteral::negate(literal);
        // We'll come back to `contains_neither` at the end.
        let (contains_negation, contains_neither): (CNFFormulaSet<T>, CNFFormulaSet<T>) =
            doesnt_contain_literal
                .into_iter()
                .partition(|clause| clause.contains(negated));

        // Now get copies of the clauses with p and ~p removed.
        let literal_complements: CNFFormulaSet<T> = contains_literal
            .iter()
            .map(|clause| {
                clause
                    .difference(&BTreeSet::from([literal.clone()]))
                    .cloned()
                    .collect()
            })
            .collect();
        let negation_complements: CNFFormulaSet<T> = contains_negation
            .iter()
            .map(|clause| {
                clause
                    .difference(&BTreeSet::from([negated.clone()]))
                    .cloned()
                    .collect()
            })
            .collect();
        let mut result = CNFFormulaSet::new();

        // Collect unions of all stripped positive and stripped negative pairs.
        for literal_comp in literal_complements.iter() {
            for negation_comp in negation_complements.iter() {
                result.insert(literal_comp | negation_comp);
            }
        }
        &Formula::strip_contradictory(&result) | &contains_neither
    }

    fn counts_containing_literal_and_negation(
        clauses: &CNFFormulaSet<T>,
        literal: &FSLiteral<T>,
    ) -> (usize, usize) {
        let num_containing_lit = clauses
            .iter()
            .filter(|clause| clause.contains(literal))
            .count();
        let negated = &FSLiteral::negate(literal);
        let num_containing_neg = clauses
            .iter()
            .filter(|clause| clause.contains(negated))
            .count();
        (num_containing_lit, num_containing_neg)
    }

    fn atom_resolution_cost(clauses: &CNFFormulaSet<T>, literal: &FSLiteral<T>) -> isize {
        let (pos, neg) = Formula::counts_containing_literal_and_negation(clauses, literal);

        let num_containing_lit = pos as isize;
        let num_containing_neg = neg as isize;

        num_containing_lit * num_containing_neg - (num_containing_lit + num_containing_neg)
    }

    pub fn _find_min<F>(obj: &F, domain: &BTreeSet<FSLiteral<T>>) -> Option<FSLiteral<T>>
    where
        F: Fn(&FSLiteral<T>) -> isize,
    {
        let comp = |f1: &&FSLiteral<T>, f2: &&FSLiteral<T>| -> Ordering { obj(f1).cmp(&obj(f2)) };
        domain.iter().min_by(comp).cloned()
    }

    pub fn _find_max<F>(obj: &F, domain: &BTreeSet<FSLiteral<T>>) -> Option<FSLiteral<T>>
    where
        F: Fn(&FSLiteral<T>) -> isize,
    {
        let comp = |f1: &&FSLiteral<T>, f2: &&FSLiteral<T>| -> Ordering { obj(f1).cmp(&obj(f2)) };
        domain.iter().max_by(comp).cloned()
    }

    fn _resolution_rule(clauses: &CNFFormulaSet<T>) -> CNFFormulaSet<T> {
        // Resolve whichever atom is cheapest.
        let positive_literals: BTreeSet<FSLiteral<T>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| &x | y)
            .into_iter()
            .filter(|literal| !FSLiteral::is_neg(literal))
            .collect();
        let obj = |literal: &FSLiteral<T>| Formula::atom_resolution_cost(clauses, literal);
        let literal = Formula::_find_min(&obj, &positive_literals)
            .expect("positive_literals should be non-empty");
        Formula::resolve_atom(clauses, &literal)
    }

    pub fn dp(clauses: &CNFFormulaSet<T>) -> bool {
        // The Davis-Putnam (1960) procedure.
        // Intended to be run on a FormulaSet<T> representing a CNF formula.
        if clauses.is_empty() {
            return true;
        }
        if clauses.contains(&BTreeSet::new()) {
            return false;
        }
        if let Ok(next) = Formula::_one_literal_rule(clauses) {
            return Formula::dp(&next);
        }
        if let Ok(next) = Formula::_affirmative_negative_rule(clauses) {
            return Formula::dp(&next);
        }
        let next = Formula::_resolution_rule(clauses);
        Formula::dp(&next)
    }

    pub fn dp_sat(&self) -> bool {
        Formula::dp(&Formula::to_cnf_formulaset(self))
    }
    pub fn dp_taut(&self) -> bool {
        !Formula::dp_sat(&Formula::negate(self))
    }
}

#[cfg(test)]
mod dp_tests {
    use super::*;

    #[test]
    fn test_one_literal_rule() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([FSLiteral::Pos(String::from("A"))]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let desired = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([FSLiteral::Pos(String::from("C"))]),
        ]);

        let result = Formula::_one_literal_rule(&formula_set);
        assert_eq!(result, Ok(desired));

        let formula_set_no_unit = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let result = Formula::_one_literal_rule(&formula_set_no_unit);
        assert_eq!(result, Err("No unit clauses found."))
    }

    #[test]
    fn test_one_literal_rule_single_atom() {
        let formula_set = BTreeSet::from([BTreeSet::from([FSLiteral::Pos(String::from("A"))])]);
        let result = Formula::_one_literal_rule(&formula_set);
        let desired = BTreeSet::new();
        assert_eq!(result, Ok(desired))
    }

    #[test]
    fn test_one_literal_rule_single_negated() {
        let formula_set = BTreeSet::from([BTreeSet::from([FSLiteral::Neg(String::from("A"))])]);
        let result = Formula::_one_literal_rule(&formula_set);
        let desired = BTreeSet::new();
        assert_eq!(result, Ok(desired))
    }

    #[test]
    fn test_affirmative_negative_rule_1() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([FSLiteral::Pos(String::from("A"))]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
        ]);
        let desired = BTreeSet::from([BTreeSet::from([FSLiteral::Pos(String::from("A"))])]);
        let result = Formula::_affirmative_negative_rule(&formula_set);
        assert_eq!(result, Ok(desired));
    }

    #[test]
    fn test_affirmative_negative_rule_2() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("B")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let result = Formula::_affirmative_negative_rule(&formula_set);
        let desired = Err("No strictly positively or strictly negatively occurring literals.");
        assert_eq!(result, desired);
    }

    #[test]
    fn test_affirmative_negative_rule_3() {
        let formula_set = BTreeSet::from([BTreeSet::from([FSLiteral::Neg(String::from("A"))])]);
        let result = Formula::_affirmative_negative_rule(&formula_set);
        assert_eq!(result, Ok(BTreeSet::new()))
    }
    #[test]
    fn test_resolve_atom() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("E")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let atom: FSLiteral<String> = FSLiteral::Pos(String::from("A"));
        let result = Formula::resolve_atom(&formula_set, &atom);
        // {{E}, {~C}} X  {{B, D}}
        let desired_product: CNFFormulaSet<String> = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("E")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("C")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
            ]),
        ]);
        let desired_rest: CNFFormulaSet<String> = BTreeSet::from([BTreeSet::from([
            FSLiteral::Neg(String::from("B")),
            FSLiteral::Pos(String::from("C")),
        ])]);
        let desired = &desired_product | &desired_rest;
        assert_eq!(result, desired)
    }

    #[test]
    fn test_find_min() {
        // Just use the (negative of the) length of the formula for a test optimum.
        let opt = |formula: &FSLiteral<String>| -(format!("{formula:?}").len() as isize);
        let domain = BTreeSet::from([
            FSLiteral::Pos(String::from("AB")),
            FSLiteral::Pos(String::from("ABC")),
            FSLiteral::Pos(String::from("A")),
        ]);
        let result = Formula::_find_min(&opt, &domain).unwrap();
        let desired = FSLiteral::Pos(String::from("ABC"));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_counts_containing_literal_and_negation() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("E")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("B")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("B")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let result = Formula::counts_containing_literal_and_negation(
            &formula_set,
            &FSLiteral::Pos(String::from("A")),
        );
        // (2 * 1) - 2 - 1 = -1
        let desired: (usize, usize) = (2, 1);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_resolution_rule() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);

        let result = Formula::_resolution_rule(&formula_set);
        // Check different cost values
        // cost picking:
        // A: 2 * 1 - 2 - 1 = 0
        // C: 2 * 1 - 2 - 1 = 0
        // D  1 * 1 - 1 - 1 = -1

        let desired_atom = FSLiteral::Pos(String::from("D"));
        let desired = Formula::resolve_atom(&formula_set, &desired_atom);

        assert_eq!(result, desired)
    }

    #[test]
    fn test_dp() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);

        let result = Formula::dp(&formula_set);
        let desired = false;
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dp_simple() {
        let formula_set = BTreeSet::from([BTreeSet::from([FSLiteral::Pos(String::from("A"))])]);
        assert!(Formula::dp(&formula_set));
    }

    #[test]
    fn test_dp_sat_taut_sanity() {
        assert!(Formula::dp_sat(&Formula::<String>::True));
        assert!(Formula::dp_taut(&Formula::<String>::True));
        assert!(!Formula::dp_sat(&Formula::<String>::False));
        assert!(!Formula::dp_taut(&Formula::<String>::False));
        assert!(Formula::dp_sat(&Formula::atom(&String::from("A"))));
        assert!(!Formula::dp_taut(&Formula::atom(&String::from("A"))));
    }
}

// DPLL
impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    pub fn posneg_count(clauses: &CNFFormulaSet<T>, literal: &FSLiteral<T>) -> usize {
        let (num_containing_lit, num_containing_neg) =
            Formula::counts_containing_literal_and_negation(clauses, literal);
        num_containing_lit + num_containing_neg
    }

    pub fn dpll(clauses: &CNFFormulaSet<T>) -> bool {
        // The Davis-Putnam-Logemann-Loveland (1962) procedure.
        if clauses.is_empty() {
            return true;
        }
        if clauses.contains(&BTreeSet::new()) {
            return false;
        }
        if let Ok(formula) = Formula::_one_literal_rule(clauses) {
            return Formula::dpll(&formula);
        }
        if let Ok(formula) = Formula::_affirmative_negative_rule(clauses) {
            return Formula::dpll(&formula);
        }
        // Split.
        // Splitting creates *two* formulas for DPLL of sizes
        // N + 1 each, but the next call to DPLL will call the unit clause rule
        // which will reduce each.
        let positive_literals: BTreeSet<FSLiteral<T>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| &x | y)
            .into_iter()
            .filter(|literal| !FSLiteral::is_neg(literal))
            .collect();
        // Use atom with max posneg_count
        let atom = Formula::_find_max(
            &|atom| Formula::posneg_count(clauses, atom) as isize,
            &positive_literals,
        )
        .expect("Positive literals should not be empty");
        let negated = FSLiteral::negate(&atom);
        let mut with_atom = clauses.clone();
        with_atom.insert(BTreeSet::from([atom]));
        let mut with_negated = clauses.clone();
        with_negated.insert(BTreeSet::from([negated]));
        Formula::dpll(&with_atom) || Formula::dpll(&with_negated)
    }

    pub fn dpll_sat(&self) -> bool {
        Formula::dpll(&Formula::to_cnf_formulaset(self))
    }
    pub fn dpll_taut(&self) -> bool {
        !Formula::dpll_sat(&Formula::negate(self))
    }
}

#[cfg(test)]
mod dpll_tests {
    use super::*;

    #[test]
    fn test_dpll() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);

        let result = Formula::dpll(&formula_set);
        let desired = false;
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dpll_sat_taut_sanity() {
        assert!(Formula::dpll_sat(&Formula::<String>::True));
        assert!(Formula::dpll_taut(&Formula::<String>::True));
        assert!(!Formula::dpll_sat(&Formula::<String>::False));
        assert!(!Formula::dpll_taut(&Formula::<String>::False));
        assert!(Formula::dpll_sat(&Formula::atom(&String::from("A"))));
        assert!(!Formula::dpll_taut(&Formula::atom(&String::from("A"))));
    }
}

// DPLI  ie. Iterative DPLL

#[derive(Clone, Debug, PartialEq)]
pub enum Mix {
    Guessed,
    Deduced,
}

pub type Valuation<T> = BTreeMap<T, bool>;

pub type Trail<T> = Vec<(FSLiteral<T>, Mix)>;

fn get_valuation_from_trail<T: Debug + Clone + Hash + Eq + Ord>(trail: &Trail<T>) -> Valuation<T> {
    fn get_valuation_pair<T: Debug + Clone + Hash + Eq + Ord>(lit: &FSLiteral<T>) -> (T, bool) {
        match lit {
            FSLiteral::Pos(t) => (t.to_owned(), true),
            FSLiteral::Neg(t) => (t.to_owned(), false),
        }
    }

    trail
        .iter()
        .map(|(lit, _)| get_valuation_pair(lit))
        .collect()
}

fn lit_abs<T: Debug + Clone + Hash + Eq + Ord>(lit: &FSLiteral<T>) -> FSLiteral<T> {
    let result = match lit {
        FSLiteral::Neg(p) => FSLiteral::Pos(p.to_owned()),
        _ => lit.to_owned(),
    };
    result.clone()
}

fn unit_subpropagate<T: Debug + Clone + Hash + Eq + Ord>(
    clauses: CNFFormulaSet<T>,
    mut trail_set: BTreeSet<FSLiteral<T>>,
    mut trail: Trail<T>,
) -> (CNFFormulaSet<T>, BTreeSet<FSLiteral<T>>, Trail<T>) {
    // Note:  takes ownership.
    // Filter out disjuncts that disagree with `trail_set`
    // from clauses.  If there are any new resulting unit clauses
    // add these to `trail` and `trail_set` and repeat.
    let reduced_clauses: CNFFormulaSet<T> = clauses
        .into_iter()
        .map(|clause| {
            clause
                .into_iter()
                .filter(|disjunct| !trail_set.contains(&FSLiteral::negate(disjunct)))
                .collect()
        })
        .collect();

    if reduced_clauses.contains(&BTreeSet::new()) {
        return (BTreeSet::from([BTreeSet::new()]), trail_set, trail);
    }

    let new_units: BTreeSet<FSLiteral<T>> = reduced_clauses
        .iter()
        .filter(|clause| clause.len() == 1 && !trail_set.contains(clause.first().unwrap()))
        .map(|clause| clause.first().unwrap().clone())
        .collect();

    if new_units.is_empty() {
        (reduced_clauses, trail_set, trail)
    } else {
        // Filter out all clauses that have agreeing conjuncts
        // (Not 100% sure this speeds things up....)
        // let reduced_clauses: FormulaSet<T> = reduced_clauses
        //     .into_iter()
        //     .filter(|clause| clause.is_disjoint(&new_units))
        //     .collect();

        for unit in new_units.into_iter() {
            trail.push((unit.clone(), Mix::Deduced));
            trail_set.insert(unit);
        }
        unit_subpropagate(reduced_clauses, trail_set, trail)
    }
}

pub struct DPLISolver<T: Debug + Clone + Hash + Eq + Ord> {
    clauses: CNFFormulaSet<T>,
    trail: Trail<T>,
    unassigned: PriorityQueue<FSLiteral<T>, usize>,
    sat: Option<bool>,
    scores: HashMap<FSLiteral<T>, usize>,
}

impl<T: Debug + Clone + Hash + Eq + Ord> DPLISolver<T> {
    pub fn new(clauses: &CNFFormulaSet<T>) -> DPLISolver<T> {
        let props: HashSet<FSLiteral<T>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| &x | y)
            .iter()
            .map(lit_abs)
            .collect();

        let scores: HashMap<FSLiteral<T>, usize> = props
            .into_iter()
            .map(|prop| {
                let count = Formula::posneg_count(clauses, &prop);
                (prop, count)
            })
            .collect();

        let unassigned: PriorityQueue<FSLiteral<T>, usize> = scores.clone().into_iter().collect();

        let trail = Trail::with_capacity(unassigned.len());

        DPLISolver {
            clauses: clauses.clone(),
            trail,
            unassigned,
            sat: None,
            scores,
        }
    }

    fn _reset(&mut self) {
        self.trail.clear();
        self.unassigned = self.scores.clone().into_iter().collect();
        self.sat = None;
    }

    pub fn num_props(&self) -> usize {
        self.scores.len()
    }

    fn trail_pop(&mut self) -> Option<FSLiteral<T>> {
        // Pop and add back to `self.unassigned`.
        let (lit, _mix) = self.trail.pop()?;
        let abs = lit_abs(&lit);
        self.unassigned.push(abs.clone(), self.scores[&abs]);
        Some(lit)
    }

    fn unit_propagate(&self) -> (CNFFormulaSet<T>, Trail<T>) {
        // Kick off recursive unit_subpropagation with a `trail_set` matching the incoming `trail`.
        let trail_set: BTreeSet<FSLiteral<T>> =
            self.trail.clone().into_iter().map(|pair| pair.0).collect();
        let (reduced_clauses, _, extended_trail) =
            unit_subpropagate(self.clauses.clone(), trail_set, self.trail.clone());
        (reduced_clauses, extended_trail)
    }

    fn backtrack(&mut self) {
        // Pop until we get to a Guessed value or the empty trail.
        if let Some((_, Mix::Deduced)) = self.trail.last() {
            self.trail_pop();
            self.backtrack()
        }
    }

    fn _dpli(&mut self) -> bool {
        // Start by unit propagating.  If this results in a contradiction, backtrack.
        let (simplified_clauses, extended_trail) = self.unit_propagate();

        if simplified_clauses.contains(&BTreeSet::new()) {
            // Reach a contradiction.  Must backtrack.
            self.backtrack();
            match self.trail.last() {
                // Switch parity of our last guess.  Marking as Deduced this time.
                Some((lit, Mix::Guessed)) => {
                    assert!(!FSLiteral::is_neg(lit));
                    let lit_clone = lit.clone();
                    // We don't call trail_pop here because we are going to use (its negation) again right after.
                    self.trail.pop();
                    self.trail
                        .push((FSLiteral::negate(&lit_clone), Mix::Deduced));
                    self._dpli()
                }
                // If there were no more Guesses, the clauses are not satisfiable.
                _ => false,
            }
        } else {
            // Above propagation was consistent.  Choose another variable to guess.

            // We have to remove the new trail elements from the Queue.
            // and update the official trail.
            // (We could have done this during subpropagation, but
            // then we would have to add them back if we had to backtrack.)
            let xlen = extended_trail.len();
            let num_new = xlen - self.trail.len();
            for (prop, _mix) in &extended_trail[xlen - num_new..] {
                self.unassigned.remove(&lit_abs(prop));
            }
            self.trail = extended_trail;

            // Get add the next guess if there are any left, or declare victory
            // if not.
            match self.unassigned.pop() {
                Some(optimum) => {
                    self.trail.push((optimum.0, Mix::Guessed));
                    self._dpli()
                }
                None => {
                    // Done.  Satisfiable.
                    true
                }
            }
        }
    }

    pub fn dpli_solve(&mut self) -> bool {
        self._reset();
        let sat = self._dpli();
        self.sat = Some(sat);
        sat
    }

    pub fn get_valuation(&self) -> Option<Valuation<T>> {
        match self.sat {
            Some(true) => Some(get_valuation_from_trail(&self.trail)),
            _ => None,
        }
    }

    // Backjumping / Conflict clause learning

    fn backjump(&mut self, p: &FSLiteral<T>) {
        // To be called when `p` is inconsistent with `trail`./
        let orig_trail = self.trail.clone();
        let orig_unassigned = self.unassigned.clone();
        self.backtrack();
        if let Some((_, Mix::Guessed)) = self.trail.last() {
            // Temporarity put p on the trail for purposes of calling
            // unit_propagate.
            self.trail_pop();
            self.trail.push((p.clone(), Mix::Guessed));
            self.unassigned.remove(p).unwrap();
            let (reduced_clauses, _) = self.unit_propagate();
            self.trail_pop();
            if reduced_clauses.contains(&BTreeSet::new()) {
                self.backjump(p);
                return;
            }
        }
        self.trail = orig_trail;
        self.unassigned = orig_unassigned;
    }

    fn _dplb(&mut self) -> bool {
        // Start by unit propagating.  If this results in a contradiction, backtrack.
        //
        let (simplified_clauses, extended_trail) = self.unit_propagate();

        if simplified_clauses.contains(&BTreeSet::new()) {
            // Reach a contradiction.  Must backtrack.
            self.backtrack();
            match self.trail.last() {
                // Switch parity of our last guess.  Marking as Deduced this time.
                Some((lit, Mix::Guessed)) => {
                    assert!(lit.is_pos());
                    let lit_clone = lit.clone();
                    self.trail_pop();
                    // Keep going back and removing Guesses (keeping lit_clone) until we get to a satisfiable trail.
                    self.backjump(&lit_clone);

                    // A clause of the negations of all guesses up till but not including
                    // p.  Note that those guesses are jointly consistent (were one to conjoin them),
                    // but not if we were to add `val`.
                    //
                    let mut constraint: BTreeSet<FSLiteral<T>> = self
                        .trail
                        .iter()
                        .filter(|(_, mix)| mix == &Mix::Guessed)
                        .map(|(val, _)| FSLiteral::negate(val))
                        .collect();
                    constraint.insert(FSLiteral::negate(&lit_clone));
                    self.clauses.insert(constraint);
                    self.trail
                        .push((FSLiteral::negate(&lit_clone), Mix::Deduced));
                    self.unassigned.remove(&lit_clone).unwrap();
                    self._dplb()
                }

                _ => false,
            }
        } else {
            // Above propagation was consistent.  Choose another variable to guess.
            let xlen = extended_trail.len();
            let num_new = xlen - self.trail.len();
            for (prop, _mix) in &extended_trail[xlen - num_new..] {
                self.unassigned.remove(&lit_abs(prop)).unwrap();
            }
            self.trail = extended_trail;

            match self.unassigned.pop() {
                Some(optimum) => {
                    self.trail.push((optimum.0, Mix::Guessed));
                    self._dplb()
                }
                None => {
                    // Done.  Satisfiable.
                    true
                }
            }
        }
    }

    pub fn dplb_solve(&mut self) -> bool {
        self._reset();
        let sat = self._dplb();
        self.sat = Some(sat);
        sat
    }
}

#[cfg(test)]
mod dpli_solver_tests {

    use super::*;

    fn get_empty_solver() -> DPLISolver<String> {
        DPLISolver::new(&BTreeSet::from([BTreeSet::new()]))
    }

    #[test]
    fn test_backtrack() {
        let mut solver = get_empty_solver();

        solver.trail = vec![
            (FSLiteral::Pos(String::from("E")), Mix::Deduced),
            (FSLiteral::Pos(String::from("D")), Mix::Guessed),
            (FSLiteral::Pos(String::from("C")), Mix::Deduced),
            (FSLiteral::Pos(String::from("B")), Mix::Deduced),
            (FSLiteral::Pos(String::from("A")), Mix::Guessed),
        ];

        // The following is just so we don't get a lookup error.
        solver.scores = HashMap::from([
            (FSLiteral::Pos(String::from("E")), 0),
            (FSLiteral::Pos(String::from("D")), 0),
            (FSLiteral::Pos(String::from("C")), 0),
            (FSLiteral::Pos(String::from("B")), 0),
            (FSLiteral::Pos(String::from("A")), 0),
        ]);

        solver.backtrack();

        assert_eq!(
            solver.trail.last(),
            Some(&(FSLiteral::Pos(String::from("A")), Mix::Guessed))
        );
        let desired_trail = vec![
            (FSLiteral::Pos(String::from("E")), Mix::Deduced),
            (FSLiteral::Pos(String::from("D")), Mix::Guessed),
            (FSLiteral::Pos(String::from("C")), Mix::Deduced),
            (FSLiteral::Pos(String::from("B")), Mix::Deduced),
            (FSLiteral::Pos(String::from("A")), Mix::Guessed),
        ];
        assert_eq!(solver.trail, desired_trail);

        solver.trail.pop();
        solver.backtrack();
        assert_eq!(
            solver.trail.last(),
            Some(&(FSLiteral::Pos(String::from("D")), Mix::Guessed))
        );
        let desired_trail = vec![
            (FSLiteral::Pos(String::from("E")), Mix::Deduced),
            (FSLiteral::Pos(String::from("D")), Mix::Guessed),
        ];
        assert_eq!(solver.trail, desired_trail);

        solver.trail.pop();
        solver.backtrack();
        assert_eq!(solver.trail.last(), None);
        let desired_trail = vec![];
        assert_eq!(solver.trail, desired_trail);
    }

    #[test]
    fn test_unit_propagate() {
        let mut solver = get_empty_solver();

        let clauses: CNFFormulaSet<String> = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("B")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("B")),
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("B")),
                FSLiteral::Pos(String::from("E")),
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);
        let trail: Trail<String> = Vec::from([
            (FSLiteral::Pos(String::from("A")), Mix::Guessed),
            (FSLiteral::Pos(String::from("Z")), Mix::Deduced),
        ]);
        solver.clauses = clauses;
        solver.trail = trail;
        let (result_clauses, result_trail) = solver.unit_propagate();

        let desired_clauses: CNFFormulaSet<String> = BTreeSet::from([
            BTreeSet::from([FSLiteral::Pos(String::from("B"))]),
            BTreeSet::from([FSLiteral::Neg(String::from("D"))]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("E")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);
        let desired_trail: Trail<String> = Vec::from([
            (FSLiteral::Pos(String::from("A")), Mix::Guessed),
            (FSLiteral::Pos(String::from("Z")), Mix::Deduced),
            (FSLiteral::Pos(String::from("B")), Mix::Deduced),
            (FSLiteral::Neg(String::from("D")), Mix::Deduced),
        ]);
        assert_eq!(result_clauses, desired_clauses);
        assert_eq!(result_trail, desired_trail);
    }
    #[test]
    fn test_dpli_1() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);

        let mut solver = DPLISolver::new(&formula_set);
        let result = solver.dpli_solve();
        assert!(!result);
        assert_eq!(solver.sat, Some(false));
        let valuation = solver.get_valuation();
        assert_eq!(valuation, None);
    }

    #[test]
    fn test_dpli_2() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let mut solver = DPLISolver::new(&formula_set);
        let result = solver.dpli_solve();
        assert!(result);
        assert_eq!(solver.sat, Some(true));
        let valuation = solver.get_valuation();
        let desired_valuation = BTreeMap::from([
            (String::from("A"), true),
            (String::from("C"), true),
            (String::from("D"), true),
        ]);
        assert_eq!(valuation, Some(desired_valuation));
    }

    #[test]
    fn test_dpli_3() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("E")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([FSLiteral::Neg(String::from("E"))]),
        ]);
        let mut solver = DPLISolver::new(&formula_set);
        let result = solver.dpli_solve();
        assert!(result);
        assert_eq!(solver.sat, Some(true));
        let valuation = solver.get_valuation();
        let desired_valuation = BTreeMap::from([
            (String::from("A"), false),
            (String::from("C"), true),
            (String::from("D"), false),
            (String::from("E"), false),
        ]);
        assert_eq!(valuation, Some(desired_valuation));
    }

    #[test]
    fn test_backjump() {
        let clauses: CNFFormulaSet<String> = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("B")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("B")),
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("D")),
                FSLiteral::Neg(String::from("Z")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("M")),
                FSLiteral::Neg(String::from("Y")),
            ]),
        ]);

        let scores = HashMap::from([
            (FSLiteral::Pos(String::from("A")), 0),
            (FSLiteral::Pos(String::from("B")), 0),
            (FSLiteral::Pos(String::from("D")), 0),
            (FSLiteral::Pos(String::from("F")), 0),
            (FSLiteral::Pos(String::from("R")), 0),
            (FSLiteral::Pos(String::from("Z")), 0),
            (FSLiteral::Pos(String::from("M")), 0),
            (FSLiteral::Pos(String::from("N")), 0),
            (FSLiteral::Pos(String::from("Y")), 0),
        ]);

        let p = FSLiteral::Pos(String::from("A"));
        let trail: Trail<String> = Vec::from([
            (FSLiteral::Pos(String::from("N")), Mix::Deduced),
            (FSLiteral::Neg(String::from("M")), Mix::Guessed),
            (FSLiteral::Pos(String::from("Z")), Mix::Guessed),
            (FSLiteral::Pos(String::from("F")), Mix::Guessed),
            (FSLiteral::Pos(String::from("R")), Mix::Deduced),
        ]);

        let mut solver = DPLISolver::new(&clauses);
        solver.trail = trail;
        solver.scores = scores;

        solver.backjump(&p);

        let desired: Trail<String> = Vec::from([
            (FSLiteral::Pos(String::from("N")), Mix::Deduced),
            (FSLiteral::Neg(String::from("M")), Mix::Guessed),
            (FSLiteral::Pos(String::from("Z")), Mix::Guessed),
        ]);
        assert_eq!(solver.trail, desired);
    }

    #[test]
    fn test_dplb_1() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
        ]);

        let mut solver = DPLISolver::new(&formula_set);
        let result = solver.dplb_solve();
        assert!(!result);
        assert_eq!(solver.sat, Some(false));
        let valuation = solver.get_valuation();
        assert_eq!(valuation, None);
    }

    #[test]
    fn test_dplb_2() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
        ]);
        let mut solver = DPLISolver::new(&formula_set);
        let result = solver.dplb_solve();
        assert!(result);
        assert_eq!(solver.sat, Some(true));
        let valuation = solver.get_valuation();
        let desired_valuation = BTreeMap::from([
            (String::from("A"), true),
            (String::from("C"), true),
            (String::from("D"), true),
        ]);
        assert_eq!(valuation, Some(desired_valuation));
    }

    #[test]
    fn test_dplb_3() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("E")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("D")),
                FSLiteral::Neg(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("D")),
            ]),
            BTreeSet::from([
                FSLiteral::Pos(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([
                FSLiteral::Neg(String::from("A")),
                FSLiteral::Pos(String::from("C")),
            ]),
            BTreeSet::from([FSLiteral::Neg(String::from("E"))]),
        ]);
        let mut solver = DPLISolver::new(&formula_set);
        let result = solver.dplb_solve();
        assert!(result);
        assert_eq!(solver.sat, Some(true));
        let valuation = solver.get_valuation();
        let desired_valuation = BTreeMap::from([
            (String::from("A"), false),
            (String::from("C"), true),
            (String::from("D"), false),
            (String::from("E"), false),
        ]);
        assert_eq!(valuation, Some(desired_valuation));
    }
}
