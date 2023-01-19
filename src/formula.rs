// Formula<T> class and Formula<T>-pecific parsing/printing functions
// that do *not* depend on T.  See propositional_logic and first_order_logic
// files for specific parsing/printing functions that specify T.

use std::collections::{BTreeSet, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::io::Write;

use crate::parse::{
    maybe_parse_bracketed, parse_bracketed, parse_right_infix, MaybePartialParseResult,
    MaybeSubparser, PartialParseResult, Subparser, SubparserFuncType,
};

use log::debug;

//### Formula AST ###
#[derive(Debug, PartialEq, Clone, PartialOrd, Eq, Ord, Hash)]
pub enum Formula<T: Clone + Debug + Hash + Eq + Ord> {
    // Note that using Rc would actually be preferable to Box here
    // since we will not need to mutate the inner formulas.
    // Unfortunately we currently rely heavily on #![feature(box_patterns)]
    // and that feature does not have a corresponding "rc" keyword.
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

impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    // NOTE:  The following builders take ownership.
    pub fn atom(t: T) -> Formula<T> {
        Formula::Atom(t)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn not(formula: Formula<T>) -> Formula<T> {
        Formula::Not(Box::new(formula))
    }

    pub fn and(formula1: Formula<T>, formula2: Formula<T>) -> Formula<T> {
        Formula::And(Box::new(formula1), Box::new(formula2))
    }

    pub fn or(formula1: Formula<T>, formula2: Formula<T>) -> Formula<T> {
        Formula::Or(Box::new(formula1), Box::new(formula2))
    }

    pub fn imp(formula1: Formula<T>, formula2: Formula<T>) -> Formula<T> {
        Formula::Imp(Box::new(formula1), Box::new(formula2))
    }

    pub fn iff(formula1: Formula<T>, formula2: Formula<T>) -> Formula<T> {
        Formula::Iff(Box::new(formula1), Box::new(formula2))
    }

    pub fn forall(var: &str, formula: Formula<T>) -> Formula<T> {
        Formula::Forall(String::from(var), Box::new(formula))
    }

    pub fn exists(var: &str, formula: Formula<T>) -> Formula<T> {
        Formula::Exists(String::from(var), Box::new(formula))
    }

    // NOTE:  The following might be better off as methods.
    pub fn get_and_ops(formula: &Formula<T>) -> (Formula<T>, Formula<T>) {
        if let Formula::And(box op1, box op2) = formula {
            (op1.clone(), op2.clone())
        } else {
            panic!("Expected Formula::And, received {formula:?}.");
        }
    }
    pub fn get_or_ops(formula: &Formula<T>) -> (Formula<T>, Formula<T>) {
        if let Formula::Or(box op1, box op2) = formula {
            (op1.clone(), op2.clone())
        } else {
            panic!("Expected Formula::Or, received {formula:?}.");
        }
    }
    pub fn get_imp_ops(formula: &Formula<T>) -> (Formula<T>, Formula<T>) {
        if let Formula::Imp(box op1, box op2) = formula {
            (op1.clone(), op2.clone())
        } else {
            panic!("Expected Formula::Imp, received {formula:?}.");
        }
    }
    pub fn get_iff_ops(formula: &Formula<T>) -> (Formula<T>, Formula<T>) {
        if let Formula::Iff(box op1, box op2) = formula {
            (op1.clone(), op2.clone())
        } else {
            panic!("Expected Formula::Iff, received {formula:?}.");
        }
    }

    pub fn antecedent(imp_formula: &Formula<T>) -> Formula<T> {
        Formula::get_imp_ops(imp_formula).0
    }

    pub fn consequent(imp_formula: &Formula<T>) -> Formula<T> {
        Formula::get_imp_ops(imp_formula).1
    }

    pub fn conjuncts(formula: &Formula<T>) -> Vec<Formula<T>> {
        match formula {
            Formula::And(box left_conjunct, box right_conjunct) => {
                let mut result = Formula::conjuncts(left_conjunct);
                result.append(&mut Formula::conjuncts(right_conjunct));
                result
            }
            _ => vec![formula.clone()],
        }
    }

    pub fn disjuncts(formula: &Formula<T>) -> Vec<Formula<T>> {
        match formula {
            Formula::Or(box left_conjunct, box right_conjunct) => {
                let mut result = Formula::disjuncts(left_conjunct);
                result.append(&mut Formula::disjuncts(right_conjunct));
                result
            }
            _ => vec![formula.clone()],
        }
    }

    pub fn on_atoms<F: Fn(&T) -> Formula<T>>(&self, map: &F) -> Formula<T> {
        // Computes the formula that results by replacing each of the atoms
        // in `self` with that atom's image along `map`.
        match self {
            Formula::Atom(t) => map(t),
            Formula::Not(box p) => Formula::not(p.on_atoms(map)),
            Formula::And(box p, box q) => Formula::and(p.on_atoms(map), q.on_atoms(map)),
            Formula::Or(box p, box q) => Formula::or(p.on_atoms(map), q.on_atoms(map)),
            Formula::Imp(box p, box q) => Formula::imp(p.on_atoms(map), q.on_atoms(map)),
            Formula::Iff(box p, box q) => Formula::iff(p.on_atoms(map), q.on_atoms(map)),
            Formula::Forall(var, box p) => Formula::forall(var, p.on_atoms(map)),
            Formula::Exists(var, box p) => Formula::exists(var, p.on_atoms(map)),
            _ => self.clone(),
        }
    }

    pub fn over_atoms<Agg>(&self, combine: &dyn Fn(&T, Agg) -> Agg, aggregate: Agg) -> Agg {
        // Apply an aggregator `combine` across all atoms of `self`, keeping the result
        // in `aggregate`.
        match self {
            Formula::Atom(t) => combine(t, aggregate),
            Formula::Not(box p) => p.over_atoms(combine, aggregate),
            Formula::And(box p, box q)
            | Formula::Or(box p, box q)
            | Formula::Imp(box p, box q)
            | Formula::Iff(box p, box q) => p.over_atoms(combine, q.over_atoms(combine, aggregate)),
            Formula::Forall(_, box p) | Formula::Exists(_, box p) => {
                p.over_atoms(combine, aggregate)
            }
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

    pub fn atoms(&self) -> BTreeSet<T> {
        BTreeSet::from_iter(self.atom_union(|x| x.clone()))
    }

    // May be able to extend this for quantifiers in which case we should remove the 'p"
    // from the name.  And if the quantifier version ends up being a different function,
    // then move this and `psimplify` to the `propositional_logic` module.
    fn _psimplify1(formula: &Formula<T>) -> Formula<T> {
        // Simplify formulas involving `True` or `False` (constants).  Also
        // eliminate double negations
        match formula {
            Formula::Not(box Formula::False) => Formula::True,
            Formula::Not(box Formula::True) => Formula::False,
            Formula::Not(box Formula::Not(box p)) => p.clone(),
            Formula::And(box p, box Formula::True) | Formula::And(box Formula::True, box p) => {
                p.clone()
            }
            Formula::And(_, box Formula::False) | Formula::And(box Formula::False, _) => {
                Formula::False
            }
            Formula::Or(_, box Formula::True) | Formula::Or(box Formula::True, _) => Formula::True,
            Formula::Or(box p, box Formula::False) | Formula::Or(box Formula::False, box p) => {
                p.clone()
            }
            Formula::Imp(_, box Formula::True) | Formula::Imp(box Formula::False, _) => {
                Formula::True
            }
            // The following arm is not in Harrison
            Formula::Imp(box Formula::True, box Formula::False) => Formula::False,

            Formula::Imp(box p, box Formula::False) => Formula::not(p.clone()),
            Formula::Imp(box Formula::True, box p) => p.clone(),

            // The following two arms are not in Harrison
            Formula::Iff(box Formula::True, box Formula::True)
            | Formula::Iff(box Formula::False, box Formula::False) => Formula::True,
            Formula::Iff(box Formula::True, box Formula::False)
            | Formula::Iff(box Formula::False, box Formula::True) => Formula::False,

            Formula::Iff(box Formula::True, box p) | Formula::Iff(box p, box Formula::True) => {
                p.clone()
            }
            Formula::Iff(box Formula::False, box p) | Formula::Iff(box p, box Formula::False) => {
                Formula::not(p.clone())
            }
            _ => formula.clone(),
        }
    }

    pub fn psimplify(&self) -> Formula<T> {
        // Apply `psimplify1` bottom-up to `self`.
        match self {
            Formula::Not(box p) => Formula::_psimplify1(&Formula::not(p.psimplify())),
            Formula::And(box p, box q) => {
                Formula::_psimplify1(&Formula::and(p.psimplify(), q.psimplify()))
            }
            Formula::Or(box p, box q) => {
                Formula::_psimplify1(&Formula::or(p.psimplify(), q.psimplify()))
            }
            Formula::Imp(box p, box q) => {
                Formula::_psimplify1(&Formula::imp(p.psimplify(), q.psimplify()))
            }
            Formula::Iff(box p, box q) => {
                Formula::_psimplify1(&Formula::iff(p.psimplify(), q.psimplify()))
            }
            _ => self.clone(),
        }
    }

    pub fn negative(&self) -> bool {
        matches!(self, Formula::Not(_))
    }

    pub fn negate(&self) -> Formula<T> {
        match self {
            Formula::Not(box p) => p.clone(),
            _ => Formula::not(self.clone()),
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
                .reduce(|x, y| Formula::and(x, y))
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
                .reduce(|x, y| Formula::or(x, y))
                .unwrap()
        }
    }

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
            Formula::Not(box p) => !p.eval_core(atom_eval, forall_eval, exists_eval),
            Formula::And(box p, box q) => {
                p.eval_core(atom_eval, forall_eval, exists_eval)
                    && q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Or(box p, box q) => {
                p.eval_core(atom_eval, forall_eval, exists_eval)
                    || q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Imp(box p, box q) => {
                !p.eval_core(atom_eval, forall_eval, exists_eval)
                    || q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Iff(box p, box q) => {
                p.eval_core(atom_eval, forall_eval, exists_eval)
                    == q.eval_core(atom_eval, forall_eval, exists_eval)
            }
            Formula::Forall(var, box p) => forall_eval(var, p),
            Formula::Exists(var, box p) => exists_eval(var, p),
        }
    }
}

#[cfg(test)]
mod formula_tests {
    use super::*;
    use crate::utils::to_vec_of_owned;

    // As usual we test with T = String.
    #[test]
    fn test_formula_equality_1() {
        let x: Formula<String> = Formula::<String>::False;
        let z: Formula<String> = Formula::<String>::False;
        assert_eq!(x, z);
    }

    fn test_formula_equality_2() {
        let x: Formula<String> = Formula::<String>::False;
        let z: Formula<String> = Formula::<String>::True;
        assert_ne!(x, z);
    }
    #[test]
    fn test_formula_equality_3() {
        let x: Formula<String> = Formula::iff(
            Formula::atom(String::from("hello")),
            Formula::and(
                Formula::atom(String::from("apples")),
                Formula::atom(String::from("oranges")),
            ),
        );
        let y: Formula<String> = Formula::iff(
            Formula::atom(String::from("hello")),
            Formula::and(
                Formula::atom(String::from("apples")),
                Formula::atom(String::from("oranges")),
            ),
        );
        assert_eq!(x, y);
    }
    #[test]
    fn test_formula_equality_4() {
        let x: Formula<String> = Formula::iff(
            Formula::atom(String::from("hello")),
            Formula::and(
                Formula::atom(String::from("apples")),
                Formula::atom(String::from("oranges")),
            ),
        );
        let y: Formula<String> = Formula::iff(
            Formula::atom(String::from("hello")),
            Formula::and(
                Formula::atom(String::from("apples")),
                Formula::atom(String::from("bananas")),
            ),
        );
        assert_ne!(x, y);
    }

    #[test]
    fn test_get_iff_ops_good_input() {
        let conj_left = Formula::atom(String::from("hello"));
        let conj_right = Formula::or(
            Formula::atom(String::from("apples")),
            Formula::atom(String::from("oranges")),
        );
        let good_input: Formula<String> = Formula::iff(conj_left.clone(), conj_right.clone());

        let (result_left, result_right) = Formula::get_iff_ops(&good_input);
        assert_eq!(result_left, conj_left);
        assert_eq!(result_right, conj_right);
    }

    #[test]
    #[should_panic]
    fn test_get_iff_ops_bad_input() {
        let bad_input: Formula<String> = Formula::and(
            Formula::atom(String::from("apples")),
            Formula::atom(String::from("oranges")),
        );

        Formula::get_iff_ops(&bad_input);
    }

    #[test]
    fn test_antecedent_and_consequent() {
        let ante = Formula::atom(String::from("apples"));
        let cons = Formula::atom(String::from("oranges"));
        let input: Formula<String> = Formula::imp(ante.clone(), cons.clone());
        let result_ante = Formula::antecedent(&input);
        let result_cons = Formula::consequent(&input);
        assert_eq!(result_ante, ante);
        assert_eq!(result_cons, cons);
    }

    #[test]
    fn test_conjuncts() {
        let input: Formula<String> = Formula::and(
            Formula::or(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::and(
                Formula::atom(String::from("C")),
                Formula::atom(String::from("D")),
            ),
        );
        let result_conjuncts = Formula::conjuncts(&input);
        let desired_conjuncts = vec![
            Formula::or(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::atom(String::from("C")),
            Formula::atom(String::from("D")),
        ];
        assert_eq!(result_conjuncts, desired_conjuncts);
    }

    #[test]
    fn test_disjuncts() {
        let input: Formula<String> = Formula::or(
            Formula::or(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::and(
                Formula::atom(String::from("C")),
                Formula::atom(String::from("D")),
            ),
        );
        let result_disjuncts = Formula::disjuncts(&input);
        let desired_disjuncts = vec![
            Formula::atom(String::from("A")),
            Formula::atom(String::from("B")),
            Formula::and(
                Formula::atom(String::from("C")),
                Formula::atom(String::from("D")),
            ),
        ];
        assert_eq!(result_disjuncts, desired_disjuncts);
    }

    #[test]
    fn test_on_atoms() {
        let input: Formula<String> = Formula::or(
            Formula::iff(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::forall(&String::from("some_var"), Formula::atom(String::from("C"))),
        );

        #[allow(clippy::ptr_arg)]
        fn foo(s: &String) -> Formula<String> {
            Formula::atom(s.clone() + "X")
        }

        let result = input.on_atoms(&foo);
        let desired: Formula<String> = Formula::or(
            Formula::iff(
                Formula::atom(String::from("AX")),
                Formula::atom(String::from("BX")),
            ),
            Formula::forall(&String::from("some_var"), Formula::atom(String::from("CX"))),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_over_atoms() {
        // We Let S = T = String.
        let input: Formula<String> = Formula::or(
            Formula::iff(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::forall(&String::from("some_var"), Formula::atom(String::from("A"))),
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
        let desired = to_vec_of_owned(vec!["A", "B", "A", "C", "B"]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_atom_union() {
        // We Let S = T = String.
        let input: Formula<String> = Formula::or(
            Formula::iff(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::imp(
                Formula::atom(String::from("B")),
                Formula::atom(String::from("C")),
            ),
        );

        #[allow(clippy::ptr_arg)]
        fn foo(s: &String) -> String {
            s.clone() + "X"
        }

        let result = input.atom_union(foo);
        let desired = HashSet::from_iter(to_vec_of_owned(vec!["AX", "BX", "CX"]));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_psimplify() {
        let formula = Formula::not(Formula::not(Formula::not(Formula::Atom("Hello"))));
        let result = Formula::not(Formula::Atom("Hello"));
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::not(Formula::<String>::True);
        let result = Formula::False;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::not(Formula::<String>::False);
        let result = Formula::True;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::and(Formula::True, Formula::atom("A"));
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::and(Formula::atom("A"), Formula::True);
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::and(Formula::False, Formula::atom("A"));
        let result = Formula::False;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::and(Formula::atom("A"), Formula::False);
        let result = Formula::False;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::or(Formula::True, Formula::atom("A"));
        let result = Formula::True;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::or(Formula::atom("A"), Formula::True);
        let result = Formula::True;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::or(Formula::False, Formula::atom("A"));
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::or(Formula::atom("A"), Formula::False);
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::imp(Formula::True, Formula::atom("A"));
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::imp(Formula::atom("A"), Formula::True);
        let result = Formula::True;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::imp(Formula::False, Formula::atom("A"));
        let result = Formula::True;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::imp(Formula::atom("A"), Formula::False);
        let result = Formula::not(Formula::atom("A"));
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::iff(Formula::True, Formula::atom("A"));
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::iff(Formula::atom("A"), Formula::True);
        let result = Formula::atom("A");
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::iff(Formula::False, Formula::atom("A"));
        let result = Formula::not(Formula::atom("A"));
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::iff(Formula::atom("A"), Formula::False);
        let result = Formula::not(Formula::atom("A"));
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::or(
            Formula::and(Formula::False, Formula::False),
            Formula::imp(Formula::False, Formula::atom("B")),
        );
        let result = Formula::True;
        assert_eq!(formula.psimplify(), result);

        let formula = Formula::imp(
            Formula::imp(
                Formula::True,
                Formula::iff(Formula::atom("x"), Formula::False),
            ),
            Formula::not(Formula::or(
                Formula::atom("y"),
                Formula::and(Formula::False, Formula::atom("z")),
            )),
        );
        let result = Formula::imp(
            Formula::not(Formula::atom("x")),
            Formula::not(Formula::atom("y")),
        );
        assert_eq!(formula.psimplify(), result);

        // Iff(False, False)),
        let formula = Formula::iff(Formula::<String>::False, Formula::<String>::False);
        let result = Formula::<String>::True;
        assert_eq!(formula.psimplify(), result);
    }

    #[test]
    fn test_negate() {
        let formula = Formula::Atom("A");
        assert_eq!(formula.negate(), Formula::not(Formula::Atom("A")));
        let formula = Formula::not(Formula::Atom("A"));
        assert_eq!(formula.negate(), Formula::Atom("A"));
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
                Formula::and(Formula::Atom("A"), Formula::Atom("B")),
                Formula::Atom("C")
            )
        );

        assert_eq!(Formula::list_disj(&empty), Formula::<String>::False);
        assert_eq!(Formula::list_disj(&singleton), Formula::Atom("A"));
        assert_eq!(
            Formula::list_disj(&multiple),
            Formula::or(
                Formula::or(Formula::Atom("A"), Formula::Atom("B")),
                Formula::Atom("C")
            )
        );
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

        formula = Formula::not(Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::not(Formula::True);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(Formula::True, Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(Formula::False, Formula::True);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(Formula::True, Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::and(Formula::False, Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(Formula::True, Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(Formula::False, Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(Formula::True, Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::or(Formula::False, Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(Formula::True, Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(Formula::False, Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(Formula::True, Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::imp(Formula::False, Formula::False);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(Formula::True, Formula::True);
        assert!(formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(Formula::False, Formula::True);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(Formula::True, Formula::False);
        assert!(!formula.eval_core(&empty, &qempty, &qempty));

        formula = Formula::iff(Formula::False, Formula::False);
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

        formula = Formula::atom("A".to_string());
        assert!(formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval));

        formula = Formula::atom("B".to_string());
        assert!(!formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval));

        formula = Formula::iff(
            Formula::atom("C".to_string()),
            Formula::and(
                Formula::atom("A".to_string()),
                Formula::atom("B".to_string()),
            ),
        );
        assert!(!formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval));

        // Should be equivalent to just And(B, C) since quantifier sub-eval ignores quantifiers.
        formula = Formula::exists(
            "X",
            Formula::and(
                Formula::atom("B".to_string()),
                Formula::forall("Y", Formula::atom("C".to_string())),
            ),
        );
        assert!(!formula.eval_core(&atom_eval, &quantifier_eval, &quantifier_eval),)
    }
}

// ### Formula Parsing ###

fn parse_atomic_formula<'a, T: Clone + Debug + Hash + Eq + Ord>(
    // A better name may be "parse_unary" or "parse_all_but_binary_connectives".
    infix_parser: for<'b> fn(&[String], &'b [String]) -> MaybePartialParseResult<'b, Formula<T>>,
    atom_parser: for<'b> fn(&[String], &'b [String]) -> PartialParseResult<'b, Formula<T>>,
    variables: &[String],
    input: &'a [String],
) -> PartialParseResult<'a, Formula<T>> {
    debug!(
        "parse_atomic_formula called on variables {:?}, input {:?}",
        variables, input
    );
    match input {
        [] => {
            panic!("Formula expected.");
        }
        [head, rest @ ..] if head == "false" => (Formula::False, rest),
        [head, rest @ ..] if head == "true" => (Formula::True, rest),
        [head, rest @ ..] if head == "(" => {
            // First try infix and if fail, fall back to parse_formula.
            let r = maybe_parse_bracketed(
                MaybeSubparser {
                    fun: &|sub_input| infix_parser(variables, sub_input),
                },
                rest,
            );
            match r {
                Ok(result) => result,
                Err(_) => parse_bracketed(
                    Subparser {
                        fun: &|sub_input| {
                            parse_formula(infix_parser, atom_parser, variables, sub_input)
                        },
                    },
                    rest,
                ),
            }
        }
        [head, rest @ ..] if head == "~" => {
            let (ast, rest1) = parse_atomic_formula(infix_parser, atom_parser, variables, rest);
            (Formula::not(ast), rest1)
        }
        [head, var, rest @ ..] if head == "forall" => {
            let mut variables = variables.to_owned();
            variables.push(String::from(var));
            parse_quantified(
                infix_parser,
                atom_parser,
                &variables,
                Formula::forall,
                var,
                rest,
            )
        }
        [head, var, rest @ ..] if head == "exists" => {
            let mut variables = variables.to_owned();
            variables.push(String::from(var));
            parse_quantified(
                infix_parser,
                atom_parser,
                &variables,
                Formula::exists,
                var,
                rest,
            )
        }
        _ => atom_parser(variables, input),
    }
}

fn parse_quantified<'a, T: Clone + Debug + Hash + Eq + Ord>(
    infix_parser: for<'b> fn(&[String], &'b [String]) -> MaybePartialParseResult<'b, Formula<T>>,
    atom_parser: for<'b> fn(&[String], &'b [String]) -> PartialParseResult<'b, Formula<T>>,
    variables: &[String],
    constructor: fn(&str, Formula<T>) -> Formula<T>,
    variable: &String,
    input: &'a [String],
) -> PartialParseResult<'a, Formula<T>> {
    debug!(
        "parse_quantified called on variables {:?}, variable {:?}, input {:?}",
        variables, variable, input
    );
    match input {
        [head, rest @ ..] => {
            let (head1, rest1) = if head == "." {
                parse_formula(infix_parser, atom_parser, variables, rest)
            } else {
                let mut variables = variables.to_owned();
                variables.push(String::from(head));
                parse_quantified(
                    infix_parser,
                    atom_parser,
                    &variables,
                    constructor,
                    head,
                    rest,
                )
            };
            (constructor(variable, head1), rest1)
        }
        _ => {
            panic!("Body of quantified term unexpected");
        }
    }
}

pub fn parse_formula<'a, T: Clone + Debug + Hash + Eq + Ord>(
    infix_parser: for<'b> fn(&[String], &'b [String]) -> MaybePartialParseResult<'b, Formula<T>>,
    atom_parser: for<'b> fn(&[String], &'b [String]) -> PartialParseResult<'b, Formula<T>>,
    variables: &[String],
    input: &'a [String],
) -> PartialParseResult<'a, Formula<T>> {
    debug!(
        "parse_formula called on variables {:?}, input {:?}",
        variables, input
    );
    // A better name might be "parse_binary_connectives".
    let atomic_subparser: SubparserFuncType<Formula<T>> =
        &|input| parse_atomic_formula(infix_parser, atom_parser, variables, input);
    let and_subparser: SubparserFuncType<Formula<T>> = &|input| {
        parse_right_infix(
            "/\\",
            Formula::and,
            Subparser {
                fun: atomic_subparser,
            },
            input,
        )
    };
    let or_subparser: SubparserFuncType<Formula<T>> = &|input| {
        let (result, rest) =
            parse_right_infix("\\/", Formula::or, Subparser { fun: and_subparser }, input);
        (result, rest)
    };
    let imp_subparser: SubparserFuncType<Formula<T>> =
        &|input| parse_right_infix("==>", Formula::imp, Subparser { fun: or_subparser }, input);
    let iff_subparser: SubparserFuncType<Formula<T>> =
        &|input| parse_right_infix("<=>", Formula::iff, Subparser { fun: imp_subparser }, input);
    let parser = iff_subparser;
    parser(input)
}

#[cfg(test)]
mod generic_ast_parse_tests {
    // We let T = String for testing purposes.

    // TODO(arthur) MORE TESTS (try to cover all that is generic yet not covered
    // by the tests in parse.rs.
    use super::*;
    use crate::utils::to_vec_of_owned;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_parse_formula_basic() {
        fn _tester_infix_parser<'a>(
            _variables: &[String],
            _input: &'a [String],
        ) -> Result<PartialParseResult<'a, Formula<String>>, &'static str> {
            Err("Infix operations not supported.")
        }

        fn _tester_atom_parser<'a>(
            _variables: &[String],
            input: &'a [String],
        ) -> PartialParseResult<'a, Formula<String>> {
            match input {
                [p, rest @ ..] if p != "(" => (Formula::atom(String::from(p)), rest),
                _ => panic!("Failed to parse propvar."),
            }
        }

        let variables = &vec![];

        let input_vec: Vec<String> = to_vec_of_owned(vec!["(", "b", "\\/", "c", ")", "==>", "a"]);

        let input: &[String] = &input_vec[..];

        let result: PartialParseResult<Formula<String>> =
            parse_formula(_tester_infix_parser, _tester_atom_parser, variables, input);

        let desired_ast = Formula::imp(
            Formula::or(
                Formula::atom(String::from("b")),
                Formula::atom(String::from("c")),
            ),
            Formula::atom(String::from("a")),
        );
        let desired_rest: &[String] = &[];
        let desired = (desired_ast, desired_rest);
        assert_eq!(result, desired);
    }
}

// ### Formula Printing ###

// Note this is not as nice as Harrison's because it relies on an
// open_box, close_box, print_space, print_break as
// in Ocaml's Format module, which may take time to implement in rust.
// In the meantime, the result will all be on one line.

// Our base write function for strings.
// Can change the `dest` during testing.
pub fn write(dest: &mut impl Write, input: &str) {
    write!(dest, "{input}").expect("Unable to write");
}
#[allow(unused_variables)]
pub fn open_box(indent: u32) {
    // No-op for now
}

pub fn close_box() {
    // No-op for now
}

pub fn print_space(dest: &mut impl Write) {
    // Just print a space for now.
    write(dest, " ");
}

pub fn print_break(dest: &mut impl Write, _x: u32, _y: u32) {
    // Just print a space for now.
    write(dest, " ");
}

fn bracket<W: Write>(dest: &mut W, add_brackets: bool, indent: u32, print_action: impl Fn(&mut W)) {
    // Similar to Harrison's `bracket` function but with a unified type `print_action` arg.
    if add_brackets {
        write(dest, "(");
    }
    open_box(indent);
    print_action(dest);
    close_box();
    if add_brackets {
        write(dest, ")");
    }
}

fn strip_quant<T: Clone + Debug + Hash + Eq + Ord>(
    formula: &Formula<T>,
) -> (Vec<String>, Formula<T>) {
    // Remove all leading quantifiers and return tuple of quantified variables
    // and the stripped formula.
    let formula: Formula<T> = formula.clone();
    match formula {
        Formula::Forall(x, box yp @ Formula::Forall(_, _))
        | Formula::Exists(x, box yp @ Formula::Exists(_, _)) => {
            let (mut xs, q) = strip_quant(&yp);
            // NOTE: Order is reversed.
            xs.push(x);
            (xs, q)
        }
        Formula::Forall(x, box p) | Formula::Exists(x, box p) => (vec![x], p),
        _ => (vec![], formula),
    }
}

fn print_formula<T: Clone + Debug + Hash + Eq + Ord, W: Write>(
    dest: &mut W,
    pfn: &fn(&mut W, u32, &T) -> (),
    prec: u32,
    formula: &Formula<T>,
) {
    /*NOTE: This is actually Harrison's *inner* print_formula with an additional pfn argument
     *
     * prec is operator precidence
     * pfn is a subprinter taking a precedence and an atom (T). */

    match formula {
        Formula::False => write(dest, "false"),
        Formula::True => write(dest, "true"),
        Formula::Atom(t) => pfn(dest, prec, t),
        Formula::Not(p) => bracket(dest, prec > 10, 1, |d| {
            print_prefix(d, pfn, 10, "~", p);
        }),
        Formula::And(p, q) => bracket(dest, prec > 8, 0, |d| {
            print_infix(d, pfn, 8, "/\\", p, q);
        }),
        Formula::Or(p, q) => bracket(dest, prec > 6, 0, |d| {
            print_infix(d, pfn, 6, "\\/", p, q);
        }),
        Formula::Imp(p, q) => bracket(dest, prec > 4, 0, |d| {
            print_infix(d, pfn, 4, "==>", p, q);
        }),
        Formula::Iff(p, q) => bracket(dest, prec > 2, 0, |d| {
            print_infix(d, pfn, 2, "<=>", p, q);
        }),
        Formula::Forall(_, _) => bracket(dest, prec > 0, 2, |d| {
            print_quant(d, pfn, "forall", formula);
        }),
        Formula::Exists(_, _) => bracket(dest, prec > 0, 2, |d| {
            print_quant(d, pfn, "exists", formula);
        }),
    }
}

fn print_quant<T: Clone + Debug + Hash + Eq + Ord, W: Write>(
    dest: &mut W,
    pfn: &fn(&mut W, u32, &T) -> (),
    qname: &str,
    formula: &Formula<T>,
) {
    // Note that `formula` is the entire quantified formula (not just the body).
    let (mut vars, body) = strip_quant(formula);
    // `strip_quant` returns vars in reverse order.
    vars.reverse();
    write(dest, qname);
    vars.iter().for_each(|v| {
        write(dest, &(" ".to_string() + v));
    });
    write(dest, ". ");
    open_box(0);
    print_formula(dest, pfn, 0, &body);
    close_box();
}

fn print_prefix<T: Clone + Debug + Hash + Eq + Ord, W: Write>(
    dest: &mut W,
    pfn: &fn(&mut W, u32, &T) -> (),
    prec: u32,
    symbol: &str,
    inner: &Formula<T>,
) {
    write(dest, symbol);
    // let prec = prec + 1;
    // NOTE that harrison seems to think (pg 627 that we should drop be dropping
    // the parents in double negations.
    // (pg 627, "[...] so that ~(~p) is printed ~~p.")
    // but the function he gives does not do that since in incrementing here we
    // would be keeping parens in double negations.
    // Likely this increment is necessary when we get to predicate logic though.
    print_formula(dest, pfn, prec, inner);
}

fn print_infix<T: Clone + Debug + Hash + Eq + Ord, W: Write>(
    dest: &mut W,
    pfn: &fn(&mut W, u32, &T) -> (),
    prec: u32,
    symbol: &str,
    left: &Formula<T>,
    right: &Formula<T>,
) {
    // As in the double negation case, this will lead to extra brackets in A & (B & C).
    print_formula(dest, pfn, prec + 1, left);
    write(dest, &(" ".to_string() + symbol));
    print_space(dest);
    print_formula(dest, pfn, prec, right);
}

impl<T: Debug + Clone + Hash + Eq + Ord> Formula<T> {
    pub fn pprint_general<W: Write>(&self, dest: &mut W, pfn: &fn(&mut W, u32, &T) -> ()) {
        // Takes a generic Write for `dest`, e.g. one can use std::io::stdout()
        // pfn is a sub-parser for atoms (type T)
        // NOTE:  It appears that both times this is passed a `pfn`, that function
        // ignores the precidence argument (u32).  Maybe simplify the type accordingly?
        open_box(0);
        write(dest, "<<");
        open_box(0);
        print_formula(dest, pfn, 0, self);
        close_box();
        write(dest, ">>");
        close_box();
    }
}
#[cfg(test)]
mod generic_ast_print_tests {
    // We let T = String for testing purposes.

    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn test_write() {
        let mut output = Vec::new();
        write(&mut output, "TESTING");
        let output = String::from_utf8(output).expect("Not UTF-8");
        assert_eq!(output, "TESTING");
    }

    fn test_bracket_no_indent() {
        let mut output1 = Vec::new();
        let mut output2 = Vec::new();
        let test_action: fn(&mut _) -> () = |dest| {
            write(dest, "TESTING");
        };
        bracket(&mut output1, true, 0, test_action);
        bracket(&mut output2, false, 0, test_action);
        let output1 = String::from_utf8(output1).expect("Not UTF-8");
        let output2 = String::from_utf8(output2).expect("Not UTF-8");
        assert_eq!(output1, "(TESTING)");
        assert_eq!(output2, "TESTING");
    }

    #[test]
    fn test_strip_quant() {
        let formula1 = Formula::atom("Hello");
        let result1 = strip_quant(&formula1);
        let desired1 = (vec![], formula1.clone());
        assert_eq!(result1, desired1);

        let inner = Formula::atom("Hello");

        let formula2 = Formula::forall(&String::from("var1"), inner.clone());
        let result2 = strip_quant(&formula2);
        let desired2 = (vec![String::from("var1")], inner.clone());
        assert_eq!(result2, desired2);

        let formula3 = Formula::forall(
            &String::from("var2"),
            Formula::forall(&String::from("var1"), inner.clone()),
        );
        let result3 = strip_quant(&formula3);
        let desired3 = (
            vec![String::from("var1"), String::from("var2")],
            inner.clone(),
        );
        assert_eq!(result3, desired3);
    }

    fn _test_pprint_general(formula: Formula<String>, desired: &str) {
        #[allow(clippy::ptr_arg)]
        fn _test_atom_printer<W: Write>(dest: &mut W, _prec: u32, name: &String) {
            // A toy printer for `Atom<String>`s that simply prints the `String`.
            write(dest, name);
        }

        let mut output = Vec::new();
        let pfn: fn(&mut _, u32, &String) -> () = _test_atom_printer;
        formula.pprint_general(&mut output, &pfn);
        let output = String::from_utf8(output).expect("Not UTF-8");
        assert_eq!(output, desired);
    }

    #[test]
    fn test_pprint_general_single_atom() {
        let formula = Formula::atom(String::from("Hello"));
        let desired = "<<Hello>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_simple_conjunction() {
        let formula = Formula::and(
            Formula::atom(String::from("Hello")),
            Formula::atom(String::from("Goodbye")),
        );
        let desired = "<<Hello /\\ Goodbye>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_or_in_and_left() {
        // Make sure that parens are printed.
        let formula = Formula::and(
            Formula::or(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::atom(String::from("C")),
        );
        let desired = "<<(A \\/ B) /\\ C>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_or_in_and_right() {
        // Make sure that parens are printed.
        let formula = Formula::and(
            Formula::atom(String::from("C")),
            Formula::or(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
        );
        let desired = "<<C /\\ (A \\/ B)>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_or_left() {
        // Make sure that parens are not printed.
        let formula = Formula::or(
            Formula::and(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::atom(String::from("C")),
        );
        let desired = "<<A /\\ B \\/ C>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_or_right() {
        // Make sure that parens are not printed.
        let formula = Formula::or(
            Formula::atom(String::from("C")),
            Formula::and(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
        );
        let desired = "<<C \\/ A /\\ B>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_and_left() {
        let formula = Formula::and(
            Formula::and(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
            Formula::atom(String::from("C")),
        );
        let desired = "<<(A /\\ B) /\\ C>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_nested_and_in_and_right() {
        let formula = Formula::and(
            Formula::atom(String::from("C")),
            Formula::and(
                Formula::atom(String::from("A")),
                Formula::atom(String::from("B")),
            ),
        );
        let desired = "<<C /\\ A /\\ B>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_simple_quantified() {
        let formula = Formula::forall(&String::from("x"), Formula::atom(String::from("Hello")));
        let desired = "<<forall x. Hello>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_quantified_conjunction() {
        let formula = Formula::forall(
            &String::from("x"),
            Formula::and(
                Formula::atom(String::from("Hello")),
                Formula::atom(String::from("Goodbye")),
            ),
        );
        let desired = "<<forall x. Hello /\\ Goodbye>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_quantified_multivar() {
        let formula = Formula::forall(
            &String::from("var1"),
            Formula::forall(&String::from("var2"), Formula::atom(String::from("Hello"))),
        );
        let desired = "<<forall var1 var2. Hello>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_quantified_in_binary() {
        let formula = Formula::iff(
            Formula::atom(String::from("Goodbye")),
            Formula::forall(&String::from("var1"), Formula::atom(String::from("Hello"))),
        );
        let desired = "<<Goodbye <=> (forall var1. Hello)>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_negate_atom() {
        let formula = Formula::not(Formula::atom(String::from("Hello")));
        let desired = "<<~Hello>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_double_negation() {
        let formula = Formula::not(Formula::not(Formula::atom(String::from("Hello"))));
        let desired = "<<~~Hello>>";
        _test_pprint_general(formula, desired);
    }

    #[test]
    fn test_pprint_general_negate_quantified() {
        let formula = Formula::not(Formula::forall(
            &String::from("x"),
            Formula::atom(String::from("Hello")),
        ));
        let desired = "<<~(forall x. Hello)>>";
        _test_pprint_general(formula, desired);
    }
}
