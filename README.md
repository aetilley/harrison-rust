A Rust library for SAT solving and automated theorem proving. This package is a work in progress, but the following are supported:

1) datatypes/parsing/printing operations
2) eval
3) standard DNF/CNF algorithms,
4) Definitional CNF (preserving equisatisfiability) for propositional logic.
5) the DP and "naive" DPLL algorithms for testing satisfiability
6) Basic Iterative DPLL as well as Backjumping/Conflict clause learning solvers DPLI and DPLU respectively.
7) Prenex normal form
8) Skolemization
9) Herbrand methods of first-order validity checking (Gilmore and Davis-Putnam)

To run the Jupyter notebook `README.ipynb`, you will need both Jupyter
https://jupyter-notebook.readthedocs.io/en/stable/

and a Jupyter Rust kernel, e.g. https://github.com/evcxr/evcxr/blob/main/evcxr_jupyter/README.md.

`README.md` is generated from `README.ipynb` by running 
```jupyter nbconvert --execute --to markdown README.ipynb```

Acknowlegement:  This libarary was highly informed by John Harrison's text on Automated Theorem Proving (which uses Ocaml).  

(Harrison, J. (2009). Handbook of Practical Logic and Automated Reasoning. Cambridge: Cambridge University Press)





```Rust
:dep harrison_rust = {path = "."}
```


```Rust
use std::collections::{HashMap, HashSet};
use std::io::stdout;
use std::path::Path;

use harrison_rust::first_order_logic::{FOValuation, Interpretation, Language, Pred};
use harrison_rust::formula::{DPLBSolver, Formula};
use harrison_rust::propositional_logic::Prop;
use harrison_rust::sudoku::{get_board_formulas, parse_sudoku_dataset, Board};
use harrison_rust::utils::run_and_time;
```

Example 1: Simple formula


```Rust
let formula = Formula::<Prop>::parse("C \\/ D <=> (~A /\\ B)").unwrap();
formula.pprint();
println!("{}", formula.get_truthtable());
let cnf = Formula::cnf(&formula);
cnf.pprint();

println!("Is satisfiable?: {}", formula.dpll_sat());
println!("Is tautology?: {}", formula.dpll_taut());
```

    <<C \/ D <=> ~A /\ B>>


    


    A     B     C     D     | formula


    ---------------------------------


    true  true  true  true  | false


    true  true  true  false | false


    true  true  false true  | false


    true  true  false false | true


    true  false true  true  | false


    true  false true  false | false


    true  false false true  | false


    true  false false false | true


    false true  true  true  | true


    false true  true  false | true


    false true  false true  | true


    false true  false false | false


    false false true  true  | false


    false false true  false | false


    false false false true  | false


    false false false false | true


    ---------------------------------


    


    <<((((((A \/ C) \/ D) \/ ~B) /\ (B \/ ~C)) /\ (B \/ ~D)) /\ (~A \/ ~C)) /\ (~A \/ ~D)>>


    


    Is satisfiable?: true


    Is tautology?: false


Example 2: A Tautology


```Rust
let formula = Formula::<Prop>::parse("A \\/ ~A").unwrap();
formula.pprint();
println!("{}", formula.get_truthtable());

println!("Is satisfiable?: {}", formula.dpll_sat());
println!("Is tautology?: {}", formula.dpll_taut());
```

    <<A \/ ~A>>


    


    A     | formula


    ---------------


    true  | true


    false | true


    ---------------


    


    Is satisfiable?: true


    Is tautology?: true


Example 3: A Contradiction


```Rust
let formula = Formula::<Prop>::parse("~A /\\ A").unwrap();
formula.pprint();
println!("{}", formula.get_truthtable());

println!("Is satisfiable?: {}", formula.dpll_sat());
println!("Is tautology?: {}", formula.dpll_taut());
println!("Is contradiction?: {}", Formula::not(&formula).dpll_taut());
```

    <<~A /\ A>>


    


    A     | formula


    ---------------


    true  | false


    false | false


    ---------------


    


    Is satisfiable?: false


    Is tautology?: false


    Is contradiction?: true


Example 4: Formula simplification


```Rust
let formula =
    Formula::<Prop>::parse("((true ==> (x <=> false)) ==> ~(y \\/ (false /\\ z)))").unwrap();
formula.pprint();
println!("...simplifies to...");
let simplified = formula.simplify();

simplified.pprint();

let formula = Formula::<Pred>::parse(
    "forall x. ((true ==> (R(x) <=> false)) ==> exists z. exists y. ~(K(y) \\/ false))",
).unwrap();
formula.pprint();
println!("...simplifies to...");
let simplified = formula.simplify();

simplified.pprint();
```

    <<(true ==> (x <=> false)) ==> ~(y \/ false /\ z)>>


    


    ...simplifies to...


    <<~x ==> ~y>>


    


    <<forall x. ((true ==> (R(x) <=> false)) ==> (exists z y. ~(K(y) \/ false)))>>


    ...simplifies to...


    <<forall x. (~R(x) ==> (exists y. ~K(y)))>>


Example 5: Solve a hard sudoku board


```Rust
let path_str: &str = "./data/sudoku.txt";
let path: &Path = Path::new(path_str);
let boards: Vec<Board> = parse_sudoku_dataset(path, Some(1));
let clauses = get_board_formulas(&boards, 9, 3)[0].clone();
let mut solver = DPLBSolver::new(&clauses);
let num_props = solver.num_props();
println!("(Sukoku sentence has {num_props} propositional variables)");
let is_sat = run_and_time(|| solver.solve());
println!("Is satisfiable?: {is_sat}");

let formula = Formula::formulaset_to_cnf(clauses);
let check = formula.eval(&solver.get_valuation().unwrap());
println!("Check: Solution satisfies original constraints?: {check}");
```

    (Sukoku sentence has 729 propositional variables)


    Run time is 1.4603595s.


    


    Is satisfiable?: true


    Check: Solution satisfies original constraints?: true


Example 6: Arithmetic mod n (n >= 2)


```Rust
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
mult_inverse_formula.pprint();

let empty_valuation = FOValuation::new();
println!("Model:         |  Is a field?");
for n in 2..20 {
    let interpretation = integers_mod_n(n);
    let sat = mult_inverse_formula.eval(&interpretation, &empty_valuation);
    println!("Integers mod {n}:  {sat}");
}
```

    Definition of multiplicative inverses:


    <<forall x. (~x = 0 ==> (exists y. x * y = 1))>>


    Model:         |  Is a field?


    Integers mod 2:  true


    Integers mod 3:  true


    Integers mod 4:  false


    Integers mod 5:  true


    Integers mod 6:  false


    Integers mod 7:  true


    Integers mod 8:  false


    Integers mod 9:  false


    Integers mod 10:  false


    Integers mod 11:  true


    Integers mod 12:  false


    Integers mod 13:  true


    Integers mod 14:  false


    Integers mod 15:  false


    Integers mod 16:  false


    Integers mod 17:  true


    Integers mod 18:  false


    Integers mod 19:  true


Example 7: Prenex Normal Form


```Rust
let formula =
    Formula::<Pred>::parse("(exists x. F(x, z)) ==> (exists w. forall z. ~G(z, x))").unwrap();
formula.pprint();
println!("In prenex normal form:");
let result = formula.pnf();
result.pprint();
```

    <<(exists x. F(x, z)) ==> (exists w. (forall z. ~G(z, x)))>>


    In prenex normal form:


    <<forall x' z'. (~F(x', z) \/ ~G(z', x))>>


Example 8: Skolemization


```Rust
let formula = Formula::<Pred>::parse(
    "R(F(y)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) 
    \\/ exists z. ~M(F(z, w))",
)
.unwrap();
formula.pprint();
println!("Skolemized:");
let result = formula.skolemize();
result.pprint();
```

    <<R(F(y)) \/ (exists x. P(f_w(x))) /\ (exists n. (forall r y. (exists w. M(G(y, w))))) \/ (exists z. ~M(F(z, w)))>>


    Skolemized:


    <<R(F(y)) \/ P(f_w(c_x)) /\ M(G(y', f_w'(y'))) \/ ~M(F(f_z(w), w))>>


Example 9: Test a first order formula for validity (valid formula)


```Rust
let string = "(forall x y. exists z. forall w. (P(x) /\\ Q(y) ==> R(z) /\\ U(w))) 
    ==> (exists x y. (P(x) /\\ Q(y))) ==> (exists z. R(z))";
let formula = Formula::<Pred>::parse(string).unwrap();
let compute_unsat_core = true;
let max_depth = 10;
Formula::davis_putnam(&formula, compute_unsat_core, max_depth);
```

    Generating tuples for next level 0


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, c_x)) \\/ ~P(c_x)) \\/ ~Q(c_x))) /\\ ((U(c_x) \\/ ~P(c_x)) \\/ ~Q(c_x))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, c_y)) \\/ ~P(c_x)) \\/ ~Q(c_y))) /\\ ((U(c_x) \\/ ~P(c_x)) \\/ ~Q(c_y))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, c_x)) \\/ ~P(c_y)) \\/ ~Q(c_x))) /\\ ((U(c_x) \\/ ~P(c_y)) \\/ ~Q(c_x))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, c_y)) \\/ ~P(c_y)) \\/ ~Q(c_y))) /\\ ((U(c_x) \\/ ~P(c_y)) \\/ ~Q(c_y))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, c_x)) \\/ ~P(c_x)) \\/ ~Q(c_x))) /\\ ((U(c_y) \\/ ~P(c_x)) \\/ ~Q(c_x))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, c_y)) \\/ ~P(c_x)) \\/ ~Q(c_y))) /\\ ((U(c_y) \\/ ~P(c_x)) \\/ ~Q(c_y))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, c_x)) \\/ ~P(c_y)) \\/ ~Q(c_x))) /\\ ((U(c_y) \\/ ~P(c_y)) \\/ ~Q(c_x))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, c_y)) \\/ ~P(c_y)) \\/ ~Q(c_y))) /\\ ((U(c_y) \\/ ~P(c_y)) \\/ ~Q(c_y))) /\\ ~R(c_y)>>"


    Generating tuples for next level 1


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, f_z(c_x, c_x))) \\/ ~P(c_x)) \\/ ~Q(f_z(c_x, c_x)))) /\\ ((U(c_x) \\/ ~P(c_x)) \\/ ~Q(f_z(c_x, c_x)))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, f_z(c_x, c_y))) \\/ ~P(c_x)) \\/ ~Q(f_z(c_x, c_y)))) /\\ ((U(c_x) \\/ ~P(c_x)) \\/ ~Q(f_z(c_x, c_y)))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, f_z(c_y, c_x))) \\/ ~P(c_x)) \\/ ~Q(f_z(c_y, c_x)))) /\\ ((U(c_x) \\/ ~P(c_x)) \\/ ~Q(f_z(c_y, c_x)))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_x, f_z(c_y, c_y))) \\/ ~P(c_x)) \\/ ~Q(f_z(c_y, c_y)))) /\\ ((U(c_x) \\/ ~P(c_x)) \\/ ~Q(f_z(c_y, c_y)))) /\\ ~R(c_x)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, f_z(c_x, c_x))) \\/ ~P(c_y)) \\/ ~Q(f_z(c_x, c_x)))) /\\ ((U(c_x) \\/ ~P(c_y)) \\/ ~Q(f_z(c_x, c_x)))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, f_z(c_x, c_y))) \\/ ~P(c_y)) \\/ ~Q(f_z(c_x, c_y)))) /\\ ((U(c_x) \\/ ~P(c_y)) \\/ ~Q(f_z(c_x, c_y)))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, f_z(c_y, c_x))) \\/ ~P(c_y)) \\/ ~Q(f_z(c_y, c_x)))) /\\ ((U(c_x) \\/ ~P(c_y)) \\/ ~Q(f_z(c_y, c_x)))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(c_y, f_z(c_y, c_y))) \\/ ~P(c_y)) \\/ ~Q(f_z(c_y, c_y)))) /\\ ((U(c_x) \\/ ~P(c_y)) \\/ ~Q(f_z(c_y, c_y)))) /\\ ~R(c_y)>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(f_z(c_x, c_x), c_x)) \\/ ~P(f_z(c_x, c_x))) \\/ ~Q(c_x))) /\\ ((U(c_x) \\/ ~P(f_z(c_x, c_x))) \\/ ~Q(c_x))) /\\ ~R(f_z(c_x, c_x))>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(f_z(c_x, c_x), c_y)) \\/ ~P(f_z(c_x, c_x))) \\/ ~Q(c_y))) /\\ ((U(c_x) \\/ ~P(f_z(c_x, c_x))) \\/ ~Q(c_y))) /\\ ~R(f_z(c_x, c_x))>>"


    Adding new formula to set: "<<(((P(c_x) /\\ Q(c_y)) /\\ ((R(f_z(f_z(c_x, c_y), c_x)) \\/ ~P(f_z(c_x, c_y))) \\/ ~Q(c_x))) /\\ ((U(c_x) \\/ ~P(f_z(c_x, c_y))) \\/ ~Q(c_x))) /\\ ~R(f_z(c_x, c_y))>>"


    Found 2 inconsistent ground instances of skolemized negation:


    <<(((P(c_x) /\ Q(c_y)) /\ ((R(f_z(f_z(c_x, c_y), c_x)) \/ ~P(f_z(c_x, c_y))) \/ ~Q(c_x))) /\ ((U(c_x) \/ ~P(f_z(c_x, c_y))) \/ ~Q(c_x))) /\ ~R(f_z(c_x, c_y))>>


    <<(((P(c_x) /\ Q(c_y)) /\ ((R(f_z(c_x, c_y)) \/ ~P(c_x)) \/ ~Q(c_y))) /\ ((U(c_y) \/ ~P(c_x)) \/ ~Q(c_y))) /\ ~R(c_x)>>


    Formula is valid.


Example 10: Test a first order formula for validity (invalid formula)


```Rust
let string = "forall boy. exists girl. (Loves(girl, friend(boy)))";
let formula = Formula::<Pred>::parse(string).unwrap();
let compute_unsat_core = true;
let max_depth = 20;
let result = Formula::davis_putnam(&formula, compute_unsat_core, max_depth);
println!("{:?}", result);
```

    Generating tuples for next level 0


    Adding new formula to set: "<<~Loves(c_boy, friend(c_boy))>>"


    Generating tuples for next level 1


    Adding new formula to set: "<<~Loves(friend(c_boy), friend(c_boy))>>"


    Generating tuples for next level 2


    Adding new formula to set: "<<~Loves(friend(friend(c_boy)), friend(c_boy))>>"


    Generating tuples for next level 3


    Adding new formula to set: "<<~Loves(friend(friend(friend(c_boy))), friend(c_boy))>>"


    Generating tuples for next level 4


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(c_boy)))), friend(c_boy))>>"


    Generating tuples for next level 5


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(c_boy))))), friend(c_boy))>>"


    Generating tuples for next level 6


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(c_boy)))))), friend(c_boy))>>"


    Generating tuples for next level 7


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(c_boy))))))), friend(c_boy))>>"


    Generating tuples for next level 8


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))), friend(c_boy))>>"


    Generating tuples for next level 9


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy))))))))), friend(c_boy))>>"


    Generating tuples for next level 10


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))))), friend(c_boy))>>"


    Generating tuples for next level 11


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy))))))))))), friend(c_boy))>>"


    Generating tuples for next level 12


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))))))), friend(c_boy))>>"


    Generating tuples for next level 13


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 14


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 15


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy))))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 16


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 17


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy))))))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 18


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 19


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy))))))))))))))))))), friend(c_boy))>>"


    Generating tuples for next level 20


    Adding new formula to set: "<<~Loves(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(friend(c_boy)))))))))))))))))))), friend(c_boy))>>"


    After searching to bound depth 20, set of ground instances (of negation) is still satisfiable. Giving up.


    BoundReached(20)

