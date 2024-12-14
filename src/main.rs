#![feature(box_patterns)]

use std::collections::{HashMap, HashSet};
use std::io::stdout;
use std::path::Path;

use harrison_rust::first_order_logic::{FOValuation, Interpretation, Language, Pred};
use harrison_rust::formula::{DPLBSolver, Formula};
use harrison_rust::propositional_logic::Prop;
use harrison_rust::sudoku::{get_board_formulas, parse_sudoku_dataset, Board};
use harrison_rust::utils::run_repeatedly_and_average;

fn main() {
    println!("```");
    println!(
        r#"
    A Rust library for SAT solving and automated theorem proving highly informed by  
    John Harrison's text on Automated Theorem Proving.

    (Harrison, J. (2009). Handbook of Practical Logic and Automated Reasoning. Cambridge: Cambridge University Press)

    (Harrison's text uses Ocaml.)

    This package is a work in progress, but the following are supported:

    1) datatypes/parsing/printing operations
    1) `eval`
    1) standard DNF/CNF algorithms,
    1) Definitional CNF (preserving equisatisfiability) for propositional logic.
    1) the DP and "naive" DPLL algorithms for testing satisfiability
    1) Basic Iterative DPLL as well as Backjumping/Conflict clause learning solvers DPLI and DPLU respectively.
    1) Prenex normal form
    1) Skolemization
    1) Herbrand methods of first-order validity checking (Gilmore and Davis-Putnam)

    NOTE:  Currently this project RELIES ON NIGHTLY RUST for exactly one feature `box_patterns`.
    For more info, see 
    https://doc.rust-lang.org/beta/unstable-book/language-features/box-patterns.html
    
    This README is the direct print output of `main.rs` (`cargo run --release > README.md`)
    (Make sure to include the release flag and run from the top level directory.)
    
    For suggestions or questions please contact tilley@fastmail.com
    "#
    );

    println!("let mut stdout = stdout();");
    let mut stdout = stdout();

    println!("\nExample 1: Simple formula");

    println!(
        r#"
    let formula = Formula::<Prop>::parse("C \\/ D <=> (~A /\\ B)").unwrap();
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);

    // Satisfiable
    println!("Is satisfiable?: {{}}", formula.dpll_sat());
    // Not a tautology
    println!("Is tautology?: {{}}", formula.dpll_taut());
    "#
    );

    let formula = Formula::<Prop>::parse("C \\/ D <=> (~A /\\ B)").unwrap();
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);

    // Satisfiable
    println!("Is satisfiable?: {}", formula.dpll_sat());
    // Not a tautology
    println!("Is tautology?: {}", formula.dpll_taut());

    println!("\nExample 2: A Tautology");

    println!(
        r#"
    let formula = Formula::<Prop>::parse("A \\/ ~A").unwrap();
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);"

    // Satisfiable
    println!("Is satisfiable?: {{}}", formula.dpll_sat());
    // Not a tautology
    println!("Is tautology?: {{}}", formula.dpll_taut());
    "#
    );

    let formula = Formula::<Prop>::parse("A \\/ ~A").unwrap();
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);

    // Satisfiable
    println!("Is satisfiable?: {}", formula.dpll_sat());
    // Not a tautology
    println!("Is tautology?: {}", formula.dpll_taut());

    println!("\nExample 3: A Contradiction");

    println!(
        r#"
    let formula = Formula::<Prop>::parse("~A /\\ A").unwrap();
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let dnf = Formula::dnf(&formula);
    dnf.pprint(&mut stdout);   

    println!("Is satisfiable?: {{}}", formula.dpll_sat());
    println!("Is tautology?: {{}}", formula.dpll_taut());
    println!("Is contradiction?: {{}}", Formula::not(&formula).dpll_taut());
    "#
    );

    let formula = Formula::<Prop>::parse("~A /\\ A").unwrap();
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let dnf = Formula::dnf(&formula);
    dnf.pprint(&mut stdout);

    println!("Is satisfiable?: {}", formula.dpll_sat());
    println!("Is tautology?: {}", formula.dpll_taut());
    println!("Is contradiction?: {}", Formula::not(&formula).dpll_taut());

    println!("\nExample 4: Formula simplification");
    println!(
        r#"
    let formula =
        Formula::<Prop>::parse("((true ==> (x <=> false)) ==> ~(y \\/ (false /\\ z)))").unwrap();
    formula.pprint(&mut stdout);
    println!("...simplifies to...");
    let simplified = formula.simplify();

    simplified.pprint(&mut stdout);

    let formula = Formula::<Pred>::parse(
        "forall x. ((true ==> (R(x) <=> false)) ==> exists z. exists y. ~(K(y) \\/ false))",
    )
    .unwrap();
    formula.pprint(&mut stdout);
    println!("...simplifies to...");
    let simplified = formula.simplify();

    simplified.pprint(&mut stdout);
    "#
    );

    let formula =
        Formula::<Prop>::parse("((true ==> (x <=> false)) ==> ~(y \\/ (false /\\ z)))").unwrap();
    formula.pprint(&mut stdout);
    println!("...simplifies to...");
    let simplified = formula.simplify();

    simplified.pprint(&mut stdout);

    let formula = Formula::<Pred>::parse(
        "forall x. ((true ==> (R(x) <=> false)) ==> exists z. exists y. ~(K(y) \\/ false))",
    )
    .unwrap();
    formula.pprint(&mut stdout);
    println!("...simplifies to...");
    let simplified = formula.simplify();

    simplified.pprint(&mut stdout);

    println!("\nExample 5: Arithmetic mod n (n >= 2)\n");

    println!(
        r#"
    fn integers_mod_n(n: u32) -> Interpretation<u32> {{
        assert!(n > 1);

        type FuncType = dyn Fn(&[u32]) -> u32;
        type RelType = dyn Fn(&[u32]) -> bool;

        let lang = Language {{
            func: HashMap::from([
                ("+".to_string(), 2),
                ("*".to_string(), 2),
                ("0".to_string(), 0),
                ("1".to_string(), 0),
            ]),
            rel: HashMap::from([("=".to_string(), 2)]),
        }};

        let domain: HashSet<u32> = HashSet::from_iter(0..n);

        let addition = move |inputs: &[u32]| -> u32 {{ (inputs[0] + inputs[1]) % n }};
        let multiplication = move |inputs: &[u32]| -> u32 {{ (inputs[0] * inputs[1]) % n }};
        let zero = |_inputs: &[u32]| -> u32 {{ 0 }};
        let one = |_inputs: &[u32]| -> u32 {{ 1 }};

        fn equality(inputs: &[u32]) -> bool {{
            inputs[0] == inputs[1]
        }}

        let funcs: HashMap<String, Box<FuncType>> = HashMap::from([
            ("+".to_string(), Box::new(addition) as Box<FuncType>),
            ("*".to_string(), Box::new(multiplication) as Box<FuncType>),
            ("0".to_string(), Box::new(zero) as Box<FuncType>),
            ("1".to_string(), Box::new(one) as Box<FuncType>),
        ]);
        let rels: HashMap<String, Box<RelType>> =
            HashMap::from([("=".to_string(), Box::new(equality) as Box<RelType>)]);

        Interpretation::new(&lang, domain, funcs, rels)
    }}

    // Let's verify (for n < 20) that the integers mod n form a field
    // (have multiplicative inverses) if and only if n is prime.
    let mult_inverse = "forall x. (~(x = 0) ==> exists y. x * y = 1)";
    let mult_inverse_formula = Formula::<Pred>::parse(mult_inverse).unwrap();
    println!("Definition of multiplicative inverses:");
    mult_inverse_formula.pprint(&mut stdout);

    let empty_valuation = FOValuation::new();
    println!("Model:         |  Is a field?");
    for n in 2..20 {{
        let interpretation = integers_mod_n(n);
        let sat = mult_inverse_formula.eval(&interpretation, &empty_valuation);
        println!("Integers mod {{n}}:  {{sat}}");
    }}
    "#
    );

    fn integers_mod_n(n: u32) -> Interpretation<u32> {
        assert!(n > 1);

        type FuncType = dyn Fn(&[u32]) -> u32;
        type RelType = dyn Fn(&[u32]) -> bool;

        let lang = Language {
            func: HashMap::from([
                ("+".to_string(), 2),
                ("*".to_string(), 2),
                ("0".to_string(), 0),
                ("1".to_string(), 0),
            ]),
            rel: HashMap::from([("=".to_string(), 2)]),
        };

        let domain: HashSet<u32> = HashSet::from_iter(0..n);

        let addition = move |inputs: &[u32]| -> u32 { (inputs[0] + inputs[1]) % n };
        let multiplication = move |inputs: &[u32]| -> u32 { (inputs[0] * inputs[1]) % n };
        let zero = |_inputs: &[u32]| -> u32 { 0 };
        let one = |_inputs: &[u32]| -> u32 { 1 };

        fn equality(inputs: &[u32]) -> bool {
            inputs[0] == inputs[1]
        }

        let funcs: HashMap<String, Box<FuncType>> = HashMap::from([
            ("+".to_string(), Box::new(addition) as Box<FuncType>),
            ("*".to_string(), Box::new(multiplication) as Box<FuncType>),
            ("0".to_string(), Box::new(zero) as Box<FuncType>),
            ("1".to_string(), Box::new(one) as Box<FuncType>),
        ]);
        let rels: HashMap<String, Box<RelType>> =
            HashMap::from([("=".to_string(), Box::new(equality) as Box<RelType>)]);

        Interpretation::new(&lang, domain, funcs, rels)
    }

    // Let's verify (for n < 20) that the integers mod n form a field
    // (have multiplicative inverses) if and only if n is prime.
    let mult_inverse = "forall x. (~(x = 0) ==> exists y. x * y = 1)";
    let mult_inverse_formula = Formula::<Pred>::parse(mult_inverse).unwrap();
    println!("Definition of multiplicative inverses:");
    mult_inverse_formula.pprint(&mut stdout);

    let empty_valuation = FOValuation::new();
    println!("Model:         |  Is a field?");
    for n in 2..20 {
        let interpretation = integers_mod_n(n);
        let sat = mult_inverse_formula.eval(&interpretation, &empty_valuation);
        println!("Integers mod {n}:  {sat}");
    }

    println!("\nExample 6: Prenex Normal Form");
    println!(
        r#"
    let formula =
        Formula::<Pred>::parse("(exists x. F(x, z)) ==> (exists w. forall z. ~G(z, x))").unwrap();
    formula.pprint(&mut stdout);
    println!("In prenex normal form:");
    let result = formula.pnf();
    result.pprint(&mut stdout);
    "#
    );

    let formula =
        Formula::<Pred>::parse("(exists x. F(x, z)) ==> (exists w. forall z. ~G(z, x))").unwrap();
    formula.pprint(&mut stdout);
    println!("In prenex normal form:");
    let result = formula.pnf();
    result.pprint(&mut stdout);

    println!("\nExample 7: Skolemization");
    println!(
        r#"
    let formula = Formula::<Pred>::parse(
        "R(F(y)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) 
        \\/ exists z. ~M(F(z, w))",
    )
    .unwrap();
    formula.pprint(&mut stdout);
    println!("Skolemized:");
    let result = formula.skolemize();
    result.pprint(&mut stdout);
    "#
    );

    let formula = Formula::<Pred>::parse(
        "R(F(y)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) 
        \\/ exists z. ~M(F(z, w))",
    )
    .unwrap();
    formula.pprint(&mut stdout);
    println!("Skolemized:");
    let result = formula.skolemize();
    result.pprint(&mut stdout);

    println!("\nExample 8: Test a first order formula for validity.");

    println!(
        r#"(
    let string = "(forall x y. exists z. forall w. (P(x) /\\ Q(y) ==> R(z) /\\ U(w))) 
        ==> (exists x y. (P(x) /\\ Q(y))) ==> (exists z. R(z))";
    let formula = Formula::<Pred>::parse(string);
    let compute_unsat_core = true;
    // Note that this will run forever if `formula` is *not* a validity.
    let run = || {{
        Formula::davis_putnam(&formula, compute_unsat_core);
    }};
    run_repeatedly_and_average(run, 1);
    let negation = formula.negate().skolemize();
    let mut free_variables = Vec::from_iter(negation.free_variables());
    free_variables.sort();
    println!(
        "Fun Fact:  These vectors of terms are a minimal set of incompatible 
        instantiations (so call \"ground instances\") of the free variables {{free_variables:?}} in 
        the (skolemization of) the negation of the formula we desired to check for validity:"
    );
    negation.pprint(&mut stdout);
	"#
    );

    let string = "(forall x y. exists z. forall w. (P(x) /\\ Q(y) ==> R(z) /\\ U(w))) 
        ==> (exists x y. (P(x) /\\ Q(y))) ==> (exists z. R(z))";
    let formula = Formula::<Pred>::parse(string).unwrap();
    let compute_unsat_core = true;
    // Note that this will run forever if `formula` is *not* a validity.
    let run = || {
        Formula::davis_putnam(&formula, compute_unsat_core);
    };
    run_repeatedly_and_average(run, 1);
    let negation = formula.negate().skolemize();
    let mut free_variables = Vec::from_iter(negation.free_variables());
    free_variables.sort();
    println!(
        "Fun Fact:  These vectors of terms are a minimal set of incompatible 
        instantiations (so call \"ground instances\") of the free variables {free_variables:?} in 
        the (skolemization of) the negation of the formula we desired to check for validity:"
    );
    negation.pprint(&mut stdout);

    println!("\nExample 9: Solve a hard sudoku board (You should be in release mode for this.)");

    println!(
        r#"
    let path_str: &str = "./data/sudoku.txt";
    let path: &Path = Path::new(path_str);
    let boards: Vec<Board> = parse_sudoku_dataset(path, Some(1));
    let clauses = get_board_formulas(&boards, 9, 3)[0].clone();
    let mut solver = DPLBSolver::new(&clauses);
    let num_props = solver.num_props();
    println!("(A sentence in {{num_props}} propositional variables)");
    let is_sat = solver.solve();
    println!("Is satisfiable?: {{is_sat}}");
    assert!(is_sat);
    let formula = Formula::formulaset_to_formula(clauses);
    let check = formula.eval(&solver.get_valuation().unwrap());
    println!("Check: Solution satisfies original constraints?: {{check}}");
    println!("Let's use the same solver to run several times and take the average time...");
    run_repeatedly_and_average(
        || {{
            solver.solve();
        }},
        10,
    );
    "#
    );

    let path_str: &str = "./data/sudoku.txt";
    let path: &Path = Path::new(path_str);
    let boards: Vec<Board> = parse_sudoku_dataset(path, Some(1));
    let clauses = get_board_formulas(&boards, 9, 3)[0].clone();
    let mut solver = DPLBSolver::new(&clauses);
    let num_props = solver.num_props();
    println!("(A sentence in {num_props} propositional variables)");
    let is_sat = solver.solve();
    println!("Is satisfiable?: {is_sat}");
    assert!(is_sat);
    let formula = Formula::formulaset_to_formula(clauses);
    let check = formula.eval(&solver.get_valuation().unwrap());
    println!("Check: Solution satisfies original constraints?: {check}");
    println!("Let's use the same solver to run several times and take the average time...");
    run_repeatedly_and_average(
        || {
            solver.solve();
        },
        10,
    );
    println!("```");
}
