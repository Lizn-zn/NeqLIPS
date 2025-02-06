use egg::{Symbol, *};
use std::collections::{HashMap, HashSet};
use std::time::Duration;

use crate::lang::{Neq, ConstantFold, expand, get_general_rules};

pub type EGraph = egg::EGraph<Neq, ConstantFold>;
pub type Runner = egg::Runner<Neq, ConstantFold, ()>;

/// Count the number of terms in an expression decomposed by additions
fn count_num_terms(expr: &str) -> usize {
    let rec_expr: RecExpr<Neq> = expr.parse().unwrap();
    let mut count = 0;
    
    // Start from the root node and count consecutive additions
    let mut current = rec_expr.as_ref().len() - 1; // Get the root node index
    
    loop {
        match &rec_expr.as_ref()[current] {
            Neq::Add([a, _b]) => {
                count += 1;
                // Continue checking the left branch for more additions
                current = (*a).into();
            }
            _ => break,
        }
    }
    
    count
}

/// Generate an expression with n terms decomposed by additions
fn synthesize_expr(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    if n == 1 {
        return "_x1".to_string();
    }
    
    let mut expr = String::new();
    
    // Build expression from left to right: (+ (+ (+ x1 x2) x3) x4)
    expr.push_str("(+ ");
    expr.push_str("?_x1");
    
    for i in 2..=n {
        expr.push_str(" ?_x");
        expr.push_str(&i.to_string());
        expr.push(')');
        if i < n {
            expr = format!("(+ {}", expr);
        }
    }
    
    expr
}

/// For this limited pattern match, we first decompose the pattern into a sum of terms,
/// then we synthesize the expression with the same number of terms,
/// and finally we perform the pattern match.
/// This is essentially a limited version of the pattern match, or somehow guided pattern match.
pub fn match_with_limit(
    expr: &RecExpr<Neq>,
    pattern: &Pattern<Neq>,
    timeout: Duration,
) -> Vec<HashMap<Symbol, RecExpr<Neq>>> {
    let var_lst = pattern.vars();
    let expr_str = "(+ ".to_owned() + &(expr.to_string() + "0)");
    let expr : RecExpr<Neq> = expand(&expr_str).parse().unwrap();
    // let expr_num_terms = count_num_terms(&expr.to_string()) + 1;
    let pat_expr : RecExpr<Neq> = expand(&pattern.to_string()).parse().unwrap();
    let pat_num_terms = count_num_terms(&pat_expr.to_string()) + 1;
    let add_expr = synthesize_expr(pat_num_terms);
    let add_expr: Pattern<Neq> = add_expr.parse().unwrap();

    // commutativity induces too many matches, disable it
    let add_rules = vec![
        // rewrite!("add_comm"; "(+ ?a ?b)"        => "(+ ?b ?a)"), 
        rewrite!("add_assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"), 
        rewrite!("add_assoc_rev"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
    ];

    let runner = Runner::default()
        .with_iter_limit(std::usize::MAX) //
        .with_node_limit(1024) //
        .with_time_limit(timeout)
        .with_expr(&expr)
        .run(&add_rules);
    // runner.print_report();
    let root = runner.roots[0];
    let mut a_substs = vec![];
    if let Some(matches) = add_expr.search_eclass_with_limit(&runner.egraph, root, 1024) {
        for s in matches.substs {
            let mut subst = HashMap::new();
            for v in add_expr.vars() {
                let rec_expr = runner.egraph.id_to_expr(*s.get(v).unwrap());
                let nm = &v.to_string()[1..];
                subst.insert(Symbol::from(nm), rec_expr);
            }
            a_substs.push(subst);
        }
    }

    let runner = Runner::default()
        .with_iter_limit(std::usize::MAX) //
        .with_node_limit(1024) //
        .with_time_limit(timeout)
        .with_expr(&pat_expr)
        .run(&add_rules);
    // runner.print_report();
    let root = runner.roots[0];
    let mut pat_substs = vec![];
    if let Some(matches) = add_expr.search_eclass_with_limit(&runner.egraph, root, 1000) {
        for s in matches.substs {
            let mut subst = HashMap::new();
            for v in add_expr.vars() {
                let rec_expr = runner.egraph.id_to_expr(*s.get(v).unwrap());
                let nm = &v.to_string()[1..];
                subst.insert(Symbol::from(nm), rec_expr);
            }
            pat_substs.push(subst);
        }
    }

    let rules = get_general_rules();
    let mut egraph = EGraph::default();
    let mut ids: HashSet<Id> = HashSet::new();
    let mut multi_pats = vec![];
    for a_subst in a_substs.iter() {
        for pat_subst in pat_substs.iter() {
            let mut multi_pat_substs = vec![];
            for v in add_expr.vars() {
                    let nm = &v.to_string()[1..];
                    let symbol = Symbol::from(nm);
                    let a_expr = a_subst.get(&symbol).unwrap();
                    ids.insert(egraph.add_expr(&a_expr).into());
                    let a_expr : PatternAst<Neq> = a_expr.to_string().parse().unwrap();
                    let pat_expr = pat_subst.get(&symbol).unwrap();
                    let pat_expr : PatternAst<Neq> = pat_expr.to_string().parse().unwrap();
                    multi_pat_substs.push((v, pat_expr.clone()));
                    multi_pat_substs.push((v, a_expr.clone()));
            }
            multi_pats.push(multi_pat_substs);
        }
    }
    egraph.rebuild();
    let runner = Runner::default()
        .with_iter_limit(std::usize::MAX) //
        .with_node_limit(4096) //
        .with_time_limit(timeout)
        .with_egraph(egraph)
        .run(&rules);
    // runner.print_report();
    let egraph = runner.egraph;

    let mut total_substs = vec![];
    // println!("multi_pats: {:?}, ids: {:?}", multi_pats.len(), ids.len());
    for multi_pat in multi_pats.iter() {
        // single var, e.g., ?l, in the first pattern is illegal
        let fpat_len = multi_pat[0].clone().1.as_ref().as_ref().len();
        if fpat_len > 1 {        
            let multipattern = MultiPattern::<Neq>::new(multi_pat.clone());
            let mut tmp_substs = vec![];
            for id in &ids {
                if let Some(matches) = multipattern.search_eclass_with_limit(&egraph, id.clone(), 1024) {
                    for s in matches.substs {
                        let mut tmp_subst : HashMap<Symbol, RecExpr<Neq>> = HashMap::new();
                        for v in &var_lst {
                            let rec_expr = egraph.id_to_expr(*s.get(*v).unwrap());
                            let nm = &v.to_string()[1..];
                            let symbol = Symbol::from(nm);
                            tmp_subst.insert(symbol, rec_expr.clone());
                        }
                        tmp_substs.push(tmp_subst);
                    }
                }
            }
            total_substs.extend_from_slice(&tmp_substs);
        }
        if total_substs.len() > 16 {
            break;
        }
    }

    total_substs
}
