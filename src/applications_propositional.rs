use crate::formula::Formula;
use crate::propositional_logic::Prop;

// Applications

// Ramsey Theory
// Given x, y, Compute a predicate for n > R(x, y).
// (That is, for any graph of size n,
// there exists either a subgraph of size x that is fully connected or
// a subgraph of size y that is fully disconnected (the antigraph is fully connected).
// "Any graph of size n" here is will be n^2 propositional atoms ranging over logical space.
// contrained by formulas representing the contraint about subsets.
//
// fn ramsey(x: u32, y: u32, n: u32) -> Formula<Prop> {
//     // A function outputing proposition names for propositions representing
//     // that two nodes a and b are connected by an edge.
//     ...FINISH
// Adder
//

fn adder(
    x: &Formula<Prop>,
    y: &Formula<Prop>,
    z: &Formula<Prop>,
    s: &Formula<Prop>,
    c: &Formula<Prop>,
) -> Formula<Prop> {
    // Exactly one or exactly three.
    let sum = Formula::iff(
        Formula::iff(x.clone(), Formula::not(y.clone())),
        Formula::not(z.clone()),
    );
    // Equiv to at least two
    let carry = Formula::list_disj(&[
        Formula::and(x.clone(), y.clone()),
        Formula::and(x.clone(), z.clone()),
        Formula::and(y.clone(), z.clone()),
    ]);
    let result = Formula::and(Formula::iff(s.clone(), sum), Formula::iff(c.clone(), carry));
    result.psimplify()
}

pub fn ripplecarry(
    x: &Vec<Formula<Prop>>,
    y: &Vec<Formula<Prop>>,
    carry: &Vec<Formula<Prop>>,
    out: &Vec<Formula<Prop>>,
    n: usize,
) -> Formula<Prop> {
    /* Assumes that bits with greater indices in  x, y, etc correspond to
     * more significant digits
     */

    assert_eq!(x.len(), n);
    assert_eq!(y.len(), n);
    assert_eq!(carry.len(), n);
    assert_eq!(out.len(), n + 1);

    // Set initial carry bit to zero.
    let mut carry = carry.clone();
    carry.insert(0, Formula::False);

    // conjoin that out[n] <==> carry[n]
    let adders = Formula::list_conj(
        &(0..n)
            .map(|idx| adder(&x[idx], &y[idx], &carry[idx], &out[idx], &carry[idx + 1]))
            .collect::<Vec<Formula<Prop>>>(),
    );
    let final_carry_is_final_out = Formula::iff(out[n].clone(), carry[n].clone());
    let result = Formula::and(adders, final_carry_is_final_out);
    result.psimplify()
}

#[cfg(test)]
mod adder_tests {
    use super::*;

    #[test]
    fn test_adder_standard_tautologies() {
        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::True,
                &Formula::True,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::False,
                &Formula::True,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::False,
                &Formula::False,
                &Formula::True,
                &Formula::False,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::True,
                &Formula::False,
                &Formula::True,
                &Formula::False,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::False,
                &Formula::True,
                &Formula::True,
                &Formula::False,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::False,
                &Formula::False,
                &Formula::False,
                &Formula::False,
            ),
            Formula::True
        );
    }

    #[test]
    fn test_adder_some_more() {
        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::True,
                &Formula::True,
            ),
            Formula::False
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );
    }

    #[test]
    fn test_adder_prop_variables() {
        let formula = adder(
            &Formula::True,
            &Formula::atom(Prop::new("Y")),
            &Formula::True,
            &Formula::atom(Prop::new("Sum")),
            &Formula::atom(Prop::new("Carry")),
        );
        assert!(!formula.tautology());
        assert!(formula.satisfiable());
    }

    #[test]
    fn test_ripplecarry() {
        let n = 3;
        //
        // Greater indices should correspond to more significant digits so e.g.
        // 3 = (bin) [1 1 0] =
        let x = vec![Formula::True, Formula::True, Formula::False];
        // 5 = (bin) [1 0 1] =
        let y = vec![Formula::True, Formula::False, Formula::True];
        let symbolic_carry = vec![
            Formula::atom(Prop::new("C1")),
            Formula::atom(Prop::new("C2")),
            Formula::atom(Prop::new("C3")),
        ];
        let out_correct = vec![
            Formula::False,
            Formula::False,
            Formula::False,
            Formula::True,
        ]; // 0 0 0 1 (8)
        let formula = ripplecarry(&x, &y, &symbolic_carry, &out_correct, n);
        // It is possible to find carries that satisfy the Formula.
        assert!(formula.dpll_sat());
        assert!(!formula.dpll_taut());

        let out_false = vec![
            Formula::False,
            Formula::False,
            Formula::True,
            Formula::False,
        ]; // 0 0 1 0 (4)
        let formula = ripplecarry(&x, &y, &symbolic_carry, &out_false, n);
        // It is *not* possible to find carries that satisfy the Formula.
        assert!(!formula.dpll_sat());
    }
}
