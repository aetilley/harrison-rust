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
use harrison_rust::utils::run_repeatedly_and_average;
```


```Rust
let mut stdout = stdout();
```

Example 1: Simple formula


```Rust
let formula = Formula::<Prop>::parse("C \\/ D <=> (~A /\\ B)").unwrap();
formula.pprint(&mut stdout);
formula.print_truthtable(&mut stdout);
let cnf = Formula::cnf(&formula);
cnf.pprint(&mut stdout);

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
formula.pprint(&mut stdout);
formula.print_truthtable(&mut stdout);
let cnf = Formula::cnf(&formula);
cnf.pprint(&mut stdout);

println!("Is satisfiable?: {}", formula.dpll_sat());
println!("Is tautology?: {}", formula.dpll_taut());
```

    <<A \/ ~A>>


    A     | formula


    ---------------


    true  | true


    false | true


    ---------------


    <<true>>


    Is satisfiable?: true


    Is tautology?: true


Example 3: A Contradiction


```Rust
let formula = Formula::<Prop>::parse("~A /\\ A").unwrap();
formula.pprint(&mut stdout);
formula.print_truthtable(&mut stdout);
let dnf = Formula::dnf(&formula);
dnf.pprint(&mut stdout);

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


    <<false>>


    Is satisfiable?: false


    Is tautology?: false


    Is contradiction?: true


Example 4: Formula simplification


```Rust
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
```

    <<(true ==> (x <=> false)) ==> ~(y \/ false /\ z)>>


    ...simplifies to...


    <<~x ==> ~y>>


    <<forall x. ((true ==> (R(x) <=> false)) ==> (exists z y. ~(K(y) \/ false)))>>


    ...simplifies to...


    <<forall x. (~R(x) ==> (exists y. ~K(y)))>>


Example 5: Solve a hard sudoku board (You should be in release mode for this.)


```Rust
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
```

    (A sentence in 729 propositional variables)


    Is satisfiable?: true


    Check: Solution satisfies original constraints?: true


    Let's use the same solver to run several times and take the average time...


    Average time over a total of 10 runs is 371.321245ms.


    


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
mult_inverse_formula.pprint(&mut stdout);

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
formula.pprint(&mut stdout);
println!("In prenex normal form:");
let result = formula.pnf();
result.pprint(&mut stdout);
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
formula.pprint(&mut stdout);
println!("Skolemized:");
let result = formula.skolemize();
result.pprint(&mut stdout);
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

    Generating tuples for next level: 0


    Adding tuple [Fun("c_x", []), Fun("c_x", []), Fun("c_x", [])]


    1 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_x", []), Fun("c_y", [])]


    2 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_y", []), Fun("c_x", [])]


    3 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_y", []), Fun("c_y", [])]


    4 tuples in formula


    Adding tuple [Fun("c_y", []), Fun("c_x", []), Fun("c_x", [])]


    5 tuples in formula


    Adding tuple [Fun("c_y", []), Fun("c_x", []), Fun("c_y", [])]


    6 tuples in formula


    Adding tuple [Fun("c_y", []), Fun("c_y", []), Fun("c_x", [])]


    7 tuples in formula


    Adding tuple [Fun("c_y", []), Fun("c_y", []), Fun("c_y", [])]


    8 tuples in formula


    Generating tuples for next level: 1


    Adding tuple [Fun("c_x", []), Fun("c_x", []), Fun("f_z", [Fun("c_x", []), Fun("c_x", [])])]


    9 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_x", []), Fun("f_z", [Fun("c_x", []), Fun("c_y", [])])]


    10 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_x", []), Fun("f_z", [Fun("c_y", []), Fun("c_x", [])])]


    11 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_x", []), Fun("f_z", [Fun("c_y", []), Fun("c_y", [])])]


    12 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_y", []), Fun("f_z", [Fun("c_x", []), Fun("c_x", [])])]


    13 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_y", []), Fun("f_z", [Fun("c_x", []), Fun("c_y", [])])]


    14 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_y", []), Fun("f_z", [Fun("c_y", []), Fun("c_x", [])])]


    15 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("c_y", []), Fun("f_z", [Fun("c_y", []), Fun("c_y", [])])]


    16 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("f_z", [Fun("c_x", []), Fun("c_x", [])]), Fun("c_x", [])]


    17 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("f_z", [Fun("c_x", []), Fun("c_x", [])]), Fun("c_y", [])]


    18 tuples in formula


    Adding tuple [Fun("c_x", []), Fun("f_z", [Fun("c_x", []), Fun("c_y", [])]), Fun("c_x", [])]


    19 tuples in formula


    Found 2 inconsistent tuples of skolemized negation: {[Fun("c_y", []), Fun("c_x", []), Fun("c_y", [])], [Fun("c_x", []), Fun("f_z", [Fun("c_x", []), Fun("c_y", [])]), Fun("c_x", [])]}


    Formula is valid.


Example 10: Test a first order formula for validity (invalid formula)


```Rust
let string = "forall boy. exists girl. (Loves(girl, friend(boy)))";
let formula = Formula::<Pred>::parse(string).unwrap();
let compute_unsat_core = true;
let max_depth = 10;
let result = Formula::davis_putnam(&formula, compute_unsat_core, max_depth);
println!("{:?}", result);
```

    Generating tuples for next level: 0


    Adding tuple [Fun("c_boy", [])]


    1 tuples in formula


    Generating tuples for next level: 1


    Adding tuple [Fun("friend", [Fun("c_boy", [])])]


    2 tuples in formula


    Generating tuples for next level: 2


    Adding tuple [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])]


    3 tuples in formula


    Generating tuples for next level: 3


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])]


    4 tuples in formula


    Generating tuples for next level: 4


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])])]


    5 tuples in formula


    Generating tuples for next level: 5


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])])])]


    6 tuples in formula


    Generating tuples for next level: 6


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])])])])]


    7 tuples in formula


    Generating tuples for next level: 7


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])])])])])]


    8 tuples in formula


    Generating tuples for next level: 8


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])])])])])])]


    9 tuples in formula


    Generating tuples for next level: 9


    Adding tuple [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("friend", [Fun("c_boy", [])])])])])])])])])])]


    10 tuples in formula


    Generating tuples for next level: 10


    Err(HerbrandBoundReached { msg: "Reached herbrand term nesting bound of 10.  Giving up." })


Note:  You might think that you could also run a parallel process checking all models of the above language of increasing size looking for counterexamples.  While this would indeed work for the example above, it does not work in general because there are some first order formulas which have counterexamples only in infinite models.  For example consider the sentence
`forall x y. (f(x) == f(y) ==> x == y) ==> exists z. (f(z) == c))` That is, every 1-1 function is onto.
This sentence is true in all finite models but need not be true in infinite models.


```Rust

```
