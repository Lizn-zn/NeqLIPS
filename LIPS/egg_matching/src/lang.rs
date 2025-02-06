use egg::{Symbol, *};
use num::traits::Pow;
use num::{BigRational, Zero};

define_language! {
    pub enum Neq {
        "-" = Neg(Id),
        "sqrt" = Sqrt(Id),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "^" = Pow([Id; 2]),

        Const(BigRational),
        Var(Symbol),
    }
}

pub type EGraph = egg::EGraph<Neq, ConstantFold>;
pub type Rewrite = egg::Rewrite<Neq, ConstantFold>;
pub type Runner = egg::Runner<Neq, ConstantFold, ()>;

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Neq> for ConstantFold {
    type Data = Option<(BigRational, PatternAst<Neq>)>;

    fn make(egraph: &mut EGraph, enode: &Neq) -> Self::Data {
        let x = |i: &Id| {
            egraph[*i]
                .data
                .as_ref()
                .map(|d| d.0.clone())
        };
        use Neq::*;
        let data = match enode {
            Neg(a) => ((-x(a)?).into(), format!("(- {})", x(a)?).parse().unwrap()),
            Add([a, b]) => (
                (x(a)? + x(b)?).into(),
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Sub([a, b]) => (
                (x(a)? - x(b)?).into(),
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Mul([a, b]) => (
                (x(a)? * x(b)?).into(),
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Div([a, b]) if !x(b)?.is_zero() => (
                (x(a)? / x(b)?).into(),
                format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Pow([a, b]) if x(b)?.is_integer() => (
                x(a)?.pow(x(b)?.to_integer()).into(),
                format!("(^ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Const(c) => (c.clone().into(), format!("{}", c).parse().unwrap()),
            _ => return None,
        };
        Some(data)
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

}

struct ExpandCostFn;
impl CostFunction<Neq> for ExpandCostFn {
    type Cost = isize;
    fn cost<C>(&mut self, enode: &Neq, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let op_cost = match enode {
            Neq::Mul(..) => -1, // prefer multiplication
            _ => 0,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

pub fn expand(expr: impl Into<String>) -> String {
    let expr = &expr.into().parse().unwrap();
    let rules = vec![
        rewrite!("add_mul_dist"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rewrite!("mul_add_dist"; "(* (+ ?b ?c) ?a)" => "(+ (* ?a ?b) (* ?a ?c))")];
    let runner = Runner::default().with_expr(&expr).run(&rules);

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, ExpandCostFn);
    let (_best_cost, best) = extractor.find_best(root);
    // println!("cost: {}, {}", _best_cost, best.to_string());

    best.to_string()
}


fn all_not_zero<'a>(vars: &'a str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool + 'a {
    let vars = vars.split_whitespace().collect::<Vec<&'a str>>();
    move |egraph, _, subst| {
        for v in &vars {
            let v = v.parse().unwrap();
            if let Some((q, _)) = &egraph[subst[v]].data {
                if q.is_zero() {
                    return false;
                }
            }
        }
        true
    }
}

pub fn get_general_rules() -> Vec<Rewrite> {
    let mut rules = vec![
        rewrite!("add_comm"; "(+ ?a ?b)"        => "(+ ?b ?a)" if all_not_zero("?a ?b")), 
        rewrite!("mul_comm"; "(* ?a ?b)"        => "(* ?b ?a)" if all_not_zero("?a ?b")), 
        rewrite!("add_assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)" if all_not_zero("?a ?b ?c")), 
        rewrite!("add_assoc_rev"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))" if all_not_zero("?a ?b ?c")), 
        rewrite!("mul_assoc"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)" if all_not_zero("?a ?b ?c")), 
        rewrite!("mul_assoc_rev"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))" if all_not_zero("?a ?b ?c")), 
        rewrite!("sub_comm"; "(+ ?a (- ?b ?c))" => "(+ (- ?a ?c) ?b)" if all_not_zero("?a ?b ?c")), 
        rewrite!("sub_assoc"; "(+ ?a (- ?b ?c))" => "(- (+ ?a ?b) ?c)" if all_not_zero("?a ?b ?c")), 
        rewrite!("sub_assoc_rev"; "(- (+ ?a ?b) ?c)" => "(+ ?a (- ?b ?c))" if all_not_zero("?a ?b ?c")), 
        rewrite!("div_canon"; "(/ ?x ?y)" => "(* ?x (/ 1 ?y))" if all_not_zero("?x ?y")),
        rewrite!("div_canon_rev"; "(* ?x (/ 1 ?y))" => "(/ ?x ?y)" if all_not_zero("?x ?y")),
        rewrite!("add_zero"; "(+ ?a 0)" => "?a" if all_not_zero("?a")),
        rewrite!("add_zero_rev"; "?a" => "(+ ?a 0)" if all_not_zero("?a")),
        rewrite!("mul_one"; "(* ?a 1)" => "?a" if all_not_zero("?a")),
        rewrite!("mul_one_rev"; "?a" => "(* ?a 1)" if all_not_zero("?a")),
    ];
    rules.extend(rewrite!("sqrt_power"; "(sqrt ?x)" <=> "(^ ?x (/ 1 2))")); 
    rules.extend(rewrite!("pow_square"; "(^ ?x 2)" <=> "(* ?x ?x)")); 
    rules.extend(rewrite!("pow_four"; "(^ ?x 4)" <=> "(^ (^ ?x 2) 2)")); 
    rules
}