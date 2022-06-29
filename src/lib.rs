use smallvec::SmallVec;
use varisat::{CnfFormula, ExtendFormula, Lit};
///Returns a literal that is true if exactly one of the input variables is true
///This uses an efficient encoding from
///https://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
pub fn commander_exactly_one(formula: &mut CnfFormula, input_variables: &[Lit]) -> Lit {
    let numvar = input_variables.len();
    let variables;
    let mut vars = SmallVec::<[Lit; 5]>::new();
    if numvar < 6 {
        variables = input_variables;
    } else {
        let chunk_size = num::integer::div_ceil(numvar, 3);
        for chunk in input_variables.chunks(chunk_size) {
            vars.push(commander_exactly_one(formula, chunk));
        }
        variables = &vars;
    }
    let commander = formula.new_lit();
    for i in 0..variables.len() {
        //No more than one var can be true
        for j in 0..i {
            formula.add_clause(&[!variables[i], !variables[j]]);
        }
    }
    let mut with_command = SmallVec::<[Lit; 6]>::from(variables);
    with_command.push(!commander);
    formula.add_clause(&with_command); //At least one must be true if the commander is true
    for &var in variables {
        //false commander implies all false inputs
        formula.add_clause(&[commander, !var]);
    }
    commander
}
///Adds a clause requiring exactly one input variable to be true
///This uses the same efficient encoding as the commander
pub fn add_exactly_one(formula: &mut CnfFormula, input_variables: &[Lit]) {
    let commander = commander_exactly_one(formula, input_variables);
    formula.add_clause(&[commander]);
}
///Adds a clause requiring at most one input variable to be true
///This uses the same efficient encoding as the commander
pub fn add_at_most_one(formula: &mut CnfFormula, input_variables: &[Lit]) {
    let commander = commander_exactly_one(formula, input_variables);
    for &var in input_variables {
        formula.add_clause(&[commander, !var]);
    }
}

fn sort_swap(formula: &mut CnfFormula, in1: Lit, in2: Lit) -> (Lit, Lit) {
    let (out1, out2) = formula.new_lits();
    formula.add_clause(&[in1, in2, !out1]);
    formula.add_clause(&[in1, in2, !out2]);
    formula.add_clause(&[in1, !in2, !out1]);
    formula.add_clause(&[in1, !in2, out2]);
    formula.add_clause(&[!in1, in2, !out1]);
    formula.add_clause(&[!in1, in2, out2]);
    formula.add_clause(&[!in1, !in2, out1]);
    formula.add_clause(&[!in1, !in2, out2]);
    (out1, out2)
}

fn make_sorting_network(formula: &mut CnfFormula, vars: &[Lit]) -> Vec<Lit> {
    let n = vars.len();
    let swaps = match n {
        0 => Some(vec![]),
        1 => Some(vec![]),
        2 => Some(vec![(0, 1)]),
        3 => Some(vec![(0, 2), (0, 1), (1, 2)]),
        4 => Some(vec![(0, 2), (1, 3), (0, 1), (2, 3), (1, 2)]),
        5 => Some(vec![
            (0, 3),
            (1, 4),
            (0, 2),
            (1, 3),
            (0, 1),
            (2, 4),
            (1, 2),
            (3, 4),
            (2, 3),
        ]),
        6 => Some(vec![
            (0, 5),
            (1, 3),
            (2, 4),
            (1, 2),
            (3, 4),
            (0, 3),
            (2, 5),
            (0, 1),
            (2, 3),
            (4, 5),
            (1, 2),
            (3, 4),
        ]),
        7 => Some(vec![
            (0, 6),
            (2, 3),
            (4, 5),
            (0, 2),
            (1, 4),
            (3, 6),
            (0, 1),
            (2, 5),
            (3, 4),
            (1, 2),
            (4, 6),
            (2, 3),
            (4, 5),
            (1, 2),
            (3, 4),
            (5, 6),
        ]),
        _ => None,
    };
    let mut vars: Vec<Lit> = vars.iter().cloned().collect();
    match swaps {
        Some(swaps) => {
            for (l, r) in swaps {
                let (l_new, r_new) = sort_swap(formula, vars[l], vars[r]);
                vars[l] = l_new;
                vars[r] = r_new;
            }
            vars
        }
        None => {
            let padding_amount = vars.len() % 4;
            for _ in 0..padding_amount {
                let lit = formula.new_lit();
                vars.push(lit);
                formula.add_clause(&[lit]);
            }
            {
                //Sort left and right
                let mut right = vars.split_off(vars.len() / 2);
                let mut left = vars;
                right = make_sorting_network(formula, &right);
                left = make_sorting_network(formula, &left);
                left.append(&mut right);
                vars = left;
            }
            {
                let mut odds: Vec<Lit> = vars
                    .iter()
                    .enumerate()
                    .filter_map(|(i, var)| if i % 2 == 1 { Some(*var) } else { None })
                    .collect();
                let mut evens: Vec<Lit> = vars
                    .iter()
                    .enumerate()
                    .filter_map(|(i, var)| if i % 2 == 0 { Some(*var) } else { None })
                    .collect();
                odds = make_sorting_network(formula, &odds);
                evens = make_sorting_network(formula, &evens);
                assert!(odds.len() == evens.len());
                vars = Vec::new();
                for i in 0..odds.len() {
                    vars.push(evens[i]);
                    vars.push(odds[i]);
                }
            }
            for i in 1..vars.len() - 1 {
                if i % 2 == 1 {
                    let (l_new, r_new) = sort_swap(formula, vars[i], vars[i + 1]);
                    vars[i] = l_new;
                    vars[i + 1] = r_new;
                }
            }
            vars.truncate(vars.len() - padding_amount);
            vars
        }
    }
}
pub fn exactly_k(formula: &mut CnfFormula, vars: &[Lit], k: usize) {
    if k == 0 {
        for &var in vars {
            formula.add_clause(&[!var]);
        }
    } else if k == vars.len() {
        for &var in vars {
            formula.add_clause(&[var]);
        }
    } else if k == 1 {
        add_exactly_one(formula, vars);
    } else {
        let sorted = make_sorting_network(formula, vars);
        formula.add_clause(&[!sorted[vars.len() - k - 1]]);
        formula.add_clause(&[sorted[vars.len() - k]]);
    }
}
#[cfg(test)]
mod tests {
    use varisat::{CnfFormula, ExtendFormula, Lit, Solver};

    use crate::{add_at_most_one, add_exactly_one, exactly_k, make_sorting_network};
    fn solve_print(formula: &CnfFormula) -> bool {
        let mut solver = Solver::new();
        solver.add_formula(formula);
        let res = solver.solve().unwrap();
        if res {
            println!("{:?}", solver.model().unwrap());
        }
        res
    }
    #[test]
    fn basic_test() {
        let mut formula = CnfFormula::new();
        let (a, b, c, d) = formula.new_lits();
        add_exactly_one(&mut formula, &[a, b, c, d]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn exact_k_test() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(10).collect();
        exactly_k(&mut formula, &lits, 9);
        let res = solve_print(&formula);
        println!("solution is {}", res);
        assert!(res)
    }
    #[test]
    fn small_sort_test() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(20).collect();
        let sorted_lits = make_sorting_network(&mut formula, &lits);
        println!("output lits are {:?}", sorted_lits);
        formula.add_clause(&[sorted_lits[3]]);
        formula.add_clause(&[!sorted_lits[2]]);
        let res = solve_print(&formula);
        println!("solution is {}", res);
        assert!(res)
    }
    #[test]
    fn sort_test_unsat() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(20).collect();
        formula.add_clause(&[lits[2]]);
        formula.add_clause(&[lits[7]]);
        formula.add_clause(&[lits[19]]);
        formula.add_clause(&[lits[4]]);
        let sorted_lits = make_sorting_network(&mut formula, &lits);
        println!("output lits are {:?}", sorted_lits);
        formula.add_clause(&[!sorted_lits[16]]);
        let res = solve_print(&formula);
        println!("solution is {}", res);
        assert!(!res);
    }
    #[test]
    fn big_test() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(10).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[5..7]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn working_overlap() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(20).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[5..8]);
        add_exactly_one(&mut formula, &lits[7..12]);
        assert!(solve_print(&formula));
    }

    #[test]
    fn huge() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(5000).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[9..20]);
        add_exactly_one(&mut formula, &lits[19..222]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn big_unsat_test() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(10).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[5..7]);
        add_exactly_one(&mut formula, &lits[2..4]);
        assert!(!solve_print(&formula));
    }
    #[test]
    fn unsat_test() {
        let mut formula = CnfFormula::new();
        let (a, b, c, d) = formula.new_lits();
        add_exactly_one(&mut formula, &[a, b, c, d]);
        add_exactly_one(&mut formula, &[a, b]);
        add_exactly_one(&mut formula, &[c, d]);
        assert!(!solve_print(&formula));
    }
    #[test]
    fn empty_soln() {
        let mut formula = CnfFormula::new();
        let (a, b, c, d) = formula.new_lits();
        add_at_most_one(&mut formula, &[a, b, c, d]);
        add_at_most_one(&mut formula, &[a, b]);
        add_at_most_one(&mut formula, &[c, d]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn med_at_most_one() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(10).collect();
        add_at_most_one(&mut formula, &lits);
        formula.add_clause(&[lits[4]]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn unsat_at_most_one() {
        let mut formula = CnfFormula::new();
        let lits: Vec<Lit> = formula.new_lit_iter(1000).collect();
        add_at_most_one(&mut formula, &lits);
        formula.add_clause(&[lits[55]]);
        formula.add_clause(&[lits[337]]);
        assert!(!solve_print(&formula));
    }
}
