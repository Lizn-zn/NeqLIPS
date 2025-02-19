
use egg::{Symbol, *};
use std::collections::HashMap;
use std::time::Duration;
use pyo3::prelude::*;

mod lang;
use lang::{Neq, expand, get_general_rules};
mod pat;
use pat::{match_with_limit};

/// Count the total number of additions and multiplications in an expression
/// Addition and multiplication are the only operations we consider.
/// This is because comm and assoc only apply to addition and multiplication.
fn count_operations(expr: impl Into<String>) -> usize {
    let expr = expr.into().parse::<egg::RecExpr<Neq>>().unwrap();
    let mut op_cost = 0;
    
    // Check all nodes in the expression
    for node in expr.as_ref() {
        match node {
            Neq::Add([_, _]) => {
                op_cost += 1;
            }
            Neq::Mul([_, _]) => {
                op_cost += 1;
            }
            Neq::Pow([_, _]) => {
                op_cost += 1;
            }
            _ => continue,
        }
    }
    
    op_cost
}

/// c.f. https://github.com/egraphs-good/egg/blob/1b2d004f63a01256047154f51568e61317cd4e89/tests/Neq.rs#L148
/// Augmented: Apply the ematch on the original pattern and expand pattern
fn ematch_aug(
    expr: &RecExpr<Neq>,
    pattern: &Pattern<Neq>,
    timeout: Duration,
) -> Vec<HashMap<Symbol, RecExpr<Neq>>> {
    // rules for inequality proving
    let rules = get_general_rules();
    
    let runner = Runner::default()
        .with_iter_limit(std::usize::MAX) //
        .with_node_limit(2048) //
        .with_time_limit(timeout)
        .with_expr(expr)
        .run(&rules);

    // runner.print_report();

    let mut substs = vec![];
    let match_limit = 9012;
    if let Some(matches) = pattern.search_eclass_with_limit(&runner.egraph, runner.roots[0], match_limit) {
        for s in matches.substs {
            let mut subst = HashMap::new();
            for v in pattern.vars() {
                let rec_expr = runner.egraph.id_to_expr(*s.get(v).unwrap());
                let nm = &v.to_string()[1..];
                subst.insert(Symbol::from(nm), rec_expr);
            }
            substs.push(subst);
        }
    }

    let expand_pattern: Pattern<Neq> = (&expand(&pattern.to_string())).parse().unwrap();
    let match_limit = 9012;
    if let Some(matches) = expand_pattern.search_eclass_with_limit(&runner.egraph, runner.roots[0], match_limit) {
        for s in matches.substs {
            let mut subst = HashMap::new();
            for v in expand_pattern.vars() {
                let rec_expr = runner.egraph.id_to_expr(*s.get(v).unwrap());
                let nm = &v.to_string()[1..];
                subst.insert(Symbol::from(nm), rec_expr);
            }
            if !substs.contains(&subst) {
                substs.push(subst);
            }
        }
    }

    substs
}

/// Apply the ematch on the original pattern
fn ematch_standard(
    expr: &RecExpr<Neq>,
    pattern: &Pattern<Neq>,
    timeout: Duration,
) -> Vec<HashMap<Symbol, RecExpr<Neq>>> {
    // rules for inequality proving
    let rules = get_general_rules();
    
    let runner = Runner::default()
        .with_iter_limit(std::usize::MAX) //
        .with_node_limit(1024) //
        .with_time_limit(timeout)
        .with_expr(expr)
        .run(&rules);

    // runner.print_report();

    let mut substs = vec![];
    let match_limit = 9012;
    if let Some(matches) = pattern.search_eclass_with_limit(&runner.egraph, runner.roots[0], match_limit) {
        for s in matches.substs {
            let mut subst = HashMap::new();
            for v in pattern.vars() {
                let rec_expr = runner.egraph.id_to_expr(*s.get(v).unwrap());
                let nm = &v.to_string()[1..];
                subst.insert(Symbol::from(nm), rec_expr);
            }
            substs.push(subst);
        }
    }

    substs
}

/// We have the following logic to apply the pattern matching:
/// 1) if the expr or pattern is simple, use ematch_aux
/// 2) if the pattern is not well structured, use limited match
/// 3) if the pattern is well structured, use ematch_aux to find all matches
/// To determine whether the pattern is well structured, we use the following rule:
/// We expand the pattern expr and count the number of operations. 
/// If the number of operations is less than 90% of the number of operations in the expanded pattern, we consider the pattern is not well structured. 
/// For example, we consider the pattern "(* ?k (+ ?u ?v))" is well structured, but "(+ (* ?k ?u) (+ ?k ?v))" is not.
pub fn ematch(
    expr_s: impl Into<String>,
    pattern_s: impl Into<String>,
    timeout: Duration,
) -> Vec<HashMap<Symbol, RecExpr<Neq>>> {
    let expr = expr_s.into().parse::<egg::RecExpr<Neq>>().unwrap();
    let expr_ops = count_operations(&expr.to_string());
    let pattern = pattern_s.into().parse::<egg::Pattern<Neq>>().unwrap();
    let pat_ops = count_operations(&pattern.to_string());
    let expand_pat_expr : RecExpr<Neq> = expand(&pattern.to_string()).parse().unwrap();
    let expand_pat_ops = count_operations(&expand_pat_expr.to_string());
    let ast_size = AstSize.cost_rec(&expr);
    // println!("expr_op_count: {}, ast_size: {}", expr_ops, ast_size);
    // println!("pat_op_count: {}", pat_ops);
    // println!("expand_op_count: {}", expand_pat_ops);
    if (expr_ops < 24 && ast_size <= 28) || expand_pat_ops < 24 { // if the expr or pattern is simple, use ematch_aux
        // println!("use ematch_aux");
        return ematch_aug(&expr, &pattern, timeout);
    }
    else {
        if pat_ops < (expand_pat_ops * 8) / 10 { // if the pattern is well structured, use ematch_standard
            // println!("use ematch_standard");
            return ematch_standard(&expr, &pattern, timeout);
        }
        else { // if the pattern is not well structured, use match_with_limit to find all matches
            // println!("use match_with_limit");
            return match_with_limit(&expr, &pattern, timeout);
        }
    }
}

#[pyfunction]
fn rs_match(py: Python<'_>, expr: &str, pattern: &str) -> PyResult<Vec<HashMap<String, String>>> {
    py.check_signals()?;
    let substs = ematch(expr, pattern, Duration::from_secs(5));
    let mut result = Vec::new();
    for subst in substs {
        let mut map = HashMap::new();
        for (k, v) in subst {
            map.insert(k.to_string(), v.to_string());
        }
        result.push(map);
    }
    Ok(result)
}

#[pymodule]
fn pyegg(m: &Bound<'_, PyModule>) -> PyResult<()> {
    pyo3_log::init();
    m.add_function(wrap_pyfunction!(rs_match, m)?)?;
    Ok(())
}