use smallvec::SmallVec;
use varisat::{CnfFormula, Lit, ExtendFormula};
///Returns a literal that is true if exactly one of the input variables is true
///This uses an efficient encoding from
///https://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
pub fn commander_exactly_one(formula:&mut CnfFormula,input_variables:&[Lit])->Lit{
    let numvar=input_variables.len();
    let variables;
    let mut vars = SmallVec::<[Lit;5]>::new();
    if numvar<6{
        variables=input_variables;
    }else {
        let chunk_size=num::integer::div_ceil(numvar,3);
        for chunk in input_variables.chunks(chunk_size){
            vars.push(commander_exactly_one(formula, chunk));
        }
        variables=&vars;
    }
    let commander=formula.new_lit();
    for i in 0..variables.len(){//No more than one var can be true
        for j in 0..i{
            formula.add_clause(&[!variables[i],!variables[j]]);
        }
    }
    let mut with_command=SmallVec::<[Lit;6]>::from(variables);
    with_command.push(!commander);
    formula.add_clause(&with_command);//At least one must be true if the commander is true
    for &var in variables{//false commander implies all false inputs
        formula.add_clause(&[commander,!var]);
    }
    commander
}
///Adds a clause requiring exactly one input variable to be true
///This uses the same efficient encoding as the commander
pub fn add_exactly_one(formula:&mut CnfFormula,input_variables:&[Lit]){
    let commander=commander_exactly_one(formula, input_variables);
    formula.add_clause(&[commander]);
}
///Adds a clause requiring at most one input variable to be true
///This uses the same efficient encoding as the commander
pub fn add_at_most_one(formula:&mut CnfFormula,input_variables:&[Lit]){
    let commander=commander_exactly_one(formula, input_variables);
    for &var in input_variables{
        formula.add_clause(&[commander,!var]);
    }
}
#[cfg(test)]
mod tests {
    use varisat::{CnfFormula, ExtendFormula, Solver, Lit};

    use crate::{add_exactly_one, add_at_most_one};
    fn solve_print(formula:& CnfFormula)->bool{
        let mut solver = Solver::new();
        solver.add_formula(formula);
        let res=solver.solve().unwrap();
        if res{
            println!("{:?}",solver.model().unwrap());
        }
        res
    }
    #[test]
    fn basic_test(){
        let mut formula=CnfFormula::new();
        let (a,b,c,d)=formula.new_lits();
        add_exactly_one(&mut formula, &[a,b,c,d]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn big_test(){
        let mut formula=CnfFormula::new();
        let lits:Vec<Lit>=formula.new_lit_iter(10).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[5..7]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn working_overlap(){
        let mut formula=CnfFormula::new();
        let lits:Vec<Lit>=formula.new_lit_iter(20).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[5..8]);
        add_exactly_one(&mut formula, &lits[7..12]);
        assert!(solve_print(&formula));
    }

    #[test]
    fn huge(){
        let mut formula=CnfFormula::new();
        let lits:Vec<Lit>=formula.new_lit_iter(5000).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[9..20]);
        add_exactly_one(&mut formula, &lits[19..222]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn big_unsat_test(){
        let mut formula=CnfFormula::new();
        let lits:Vec<Lit>=formula.new_lit_iter(10).collect();
        add_exactly_one(&mut formula, &lits);
        add_exactly_one(&mut formula, &lits[5..7]);
        add_exactly_one(&mut formula, &lits[2..4]);
        assert!(!solve_print(&formula));
    }
    #[test]
    fn unsat_test(){
        let mut formula=CnfFormula::new();
        let (a,b,c,d)=formula.new_lits();
        add_exactly_one(&mut formula, &[a,b,c,d]);
        add_exactly_one(&mut formula, &[a,b]);
        add_exactly_one(&mut formula, &[c,d]);
        assert!(!solve_print(&formula));
    }
    #[test]
    fn empty_soln(){
        let mut formula=CnfFormula::new();
        let (a,b,c,d)=formula.new_lits();
        add_at_most_one(&mut formula, &[a,b,c,d]);
        add_at_most_one(&mut formula, &[a,b]);
        add_at_most_one(&mut formula, &[c,d]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn med_at_most_one(){
        let mut formula=CnfFormula::new();
        let lits:Vec<Lit>=formula.new_lit_iter(10).collect();
        add_at_most_one(&mut formula, &lits);
        formula.add_clause(&[lits[4]]);
        assert!(solve_print(&formula));
    }
    #[test]
    fn unsat_at_most_one(){
        let mut formula=CnfFormula::new();
        let lits:Vec<Lit>=formula.new_lit_iter(1000).collect();
        add_at_most_one(&mut formula, &lits);
        formula.add_clause(&[lits[55]]);
        formula.add_clause(&[lits[337]]);
        assert!(!solve_print(&formula));
    }
}
