#[macro_use]
extern crate lazy_static;
use std::{f64::INFINITY, sync::atomic::AtomicUsize};

use egg::*;
use std::collections::HashMap;

define_language! {
    enum SimpleLanguage {

        // string variants with an array of child `Id`s (any static size)
        // any type that implements LanguageChildren may be used here
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "**" = Exp([Id; 2]),
        "<" = Le([Id;2]),
        ">" = Gt([Id;2]),
        "<=" = Leq([Id;2]),
        ">=" = Geq([Id;2]),
        "=" = Eq([Id;2]),
        "!=" = Neq([Id;2]),
        "false" = False,
        "true" = True,

        "if" = If([Id;2]),
        "ite" = Ite([Id; 3]),
        "ite-force" = IteForced([Id;3]),
        "while" = While([Id; 3]),  // (while label cond body)
        //"while" = WhileUnrolled([Id;4]),
        "not" = Not(Id),
        "." = Access([Id; 2]),
        "let" = Let([Id; 3]),
        "begin" = Begin([Id;2]),

        // string variants with a single child `Id`
        // note that this is distinct from `Sub`, even though it has the same
        // string, because it has a different number of children
        "-"  = Neg(Id),
        "++" = Inc([Id;1]),

        Num(i32),
        //FloatNum(f64), -- FLoa does not have Hash trait

        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last
        Symbol(Symbol),
        // This is the ultimate fallback, it will parse any operator (as a string)
        // and only 2 children.
        // Note that if there were 0 children, the previous branch would have succeeded
        Other(Symbol, [Id;2]),
    }
}

struct RuntimeCostModel<'a> {
    egraph: &'a EGraph<SimpleLanguage, ()>,
}

lazy_static! {
    static ref ASSUMED_ITERATIONS: HashMap<String, i32> = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), 20);
        m
    };
    static ref UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
}

impl<'a> CostFunction<SimpleLanguage> for RuntimeCostModel<'a> {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &SimpleLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        match enode {
            SimpleLanguage::Num(_val) => 1.0,
            SimpleLanguage::False => 1.0,
            SimpleLanguage::True => 1.0,
            SimpleLanguage::Symbol(_name) => 1.0,

            SimpleLanguage::Access([_obj, _prop]) => costs(*_obj) + costs(*_prop),

            SimpleLanguage::Add([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Sub([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Mul([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Div([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Exp([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Le([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Gt([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Leq([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Geq([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Eq([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Neq([a, b]) => 1.0 + costs(*a) + costs(*b),
            SimpleLanguage::Not(val) => 1.0 + costs(*val),
            SimpleLanguage::Neg(val) => 1.0 + costs(*val),

            SimpleLanguage::IteForced([cond, left, right]) => {
                costs(*cond) + costs(*left) + costs(*right)
            }
            SimpleLanguage::Let([_var, expr, body]) => 1.0 + costs(*expr) + costs(*body),

            SimpleLanguage::While([loop_id, cond, body]) => {
                if !self
                    .egraph
                    .id_to_expr(*loop_id)
                    .to_string()
                    .as_str()
                    .starts_with("static")
                {
                    return INFINITY;
                }

                costs(*cond)
                    + (costs(*cond) + costs(*body))
                        * ASSUMED_ITERATIONS
                            .get(
                                self.egraph
                                    .id_to_expr(*loop_id)
                                    .to_string()
                                    .as_str()
                                    .split('-')
                                    .skip(3)
                                    .next()
                                    .unwrap(),
                            )
                            .map(|x| *x as f64)
                            .unwrap()
            }
            SimpleLanguage::Ite([cond, true_branch, false_branch]) => {
                if costs(*true_branch) != costs(*false_branch) {
                    return INFINITY;
                } else {
                    costs(*cond) + costs(*true_branch)
                }
            }
            SimpleLanguage::Begin(vals) => (*vals).iter().map(|x| costs(*x)).sum::<Self::Cost>(),
            SimpleLanguage::Other(_f, vals) => {
                //println!("F is {:?} and vals are {:?}", _f, vals);
                1.0 + (*vals).iter().map(|x| costs(*x)).sum::<Self::Cost>()
            }
            SimpleLanguage::If(_) => INFINITY,
            SimpleLanguage::Inc([x]) => 1.0 + costs(*x),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IFFiller {
    cond: Var,
    body: Var,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ITEFiller {
    cond: Var,
    left: Var,
    right: Var,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoopStaticiser {
    label: Var,
    cond: Var,
    body: Var,
}

fn construct_padding(cost: f64, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
    let dummy = egraph.add(SimpleLanguage::True);
    if cost <= 0.0 {
        panic!("Shoud always get non-zero value")
    } else {
        let mut body = dummy;
        let mut x = 1.0;
        while cost != x {
            x += 1.0;
            body = egraph.add(SimpleLanguage::Not(body));
        }
        return body;
    }
}

impl Applier<SimpleLanguage, ()> for IFFiller {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<SimpleLanguage, ()>,
        matched_id: Id, // Identifier of (let (?a ?b) ?c)
        subst: &Subst,
        _searcher_pattern: Option<&PatternAst<SimpleLanguage>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let a: Id = subst[self.cond];
        let b: Id = subst[self.body];

        let body = simplify_expr(egraph.id_to_expr(b)).parse().unwrap();

        let mut cost_model = RuntimeCostModel { egraph };

        let cost = cost_model.cost_rec(&body);

        //println!("I matched {}",egraph.id_to_expr(matched_id).to_string());
        
        if cost == INFINITY {
            //println!("Could not solve it, the child is infinite");
            return vec![];
        }
        //println!("Child is not infinite!");

        
        let padded_cond = SimpleLanguage::Ite([a, b, construct_padding(cost, egraph)]);

        let padded_cond_id = egraph.add(padded_cond);



        // Don't forget to union the new node with the matched node!
        if egraph.union(matched_id, padded_cond_id) {
            vec![padded_cond_id]
        } else {
            vec![]
        }
    }
}

impl Applier<SimpleLanguage, ()> for ITEFiller {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<SimpleLanguage, ()>,
        matched_id: Id, // Identifier of (let (?a ?b) ?c)
        subst: &Subst,
        _searcher_pattern: Option<&PatternAst<SimpleLanguage>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let a: Id = subst[self.cond];
        let b: Id = subst[self.left];
        let c: Id = subst[self.right];

        let left_optimal = simplify_expr(egraph.id_to_expr(b)).parse().unwrap();
        let right_optimal = simplify_expr(egraph.id_to_expr(c)).parse().unwrap();

        let mut cost_model = RuntimeCostModel { egraph };

        let cost_left = cost_model.cost_rec(&left_optimal);
        let cost_right = cost_model.cost_rec(&right_optimal);

        let left_optimal_id = egraph.add_expr(&left_optimal);

        let right_optimal_id = egraph.add_expr(&right_optimal);

        //println!("I matched {}",egraph.id_to_expr(matched_id).to_string());
        
        let mut padded_cond :Id;

        if cost_left == cost_right {
            padded_cond = egraph.add(SimpleLanguage::Ite([a, left_optimal_id, right_optimal_id]))
        }
        
        if cost_left > cost_right{
            let padding = construct_padding(cost_left-cost_right, egraph);
            let padded_right = egraph.add(SimpleLanguage::Begin([padding,right_optimal_id]));
            padded_cond = egraph.add(SimpleLanguage::Ite([a,left_optimal_id,padded_right]))
        }
        else{
            let padding = construct_padding(cost_right-cost_left, egraph);
            let padded_left = egraph.add(SimpleLanguage::Begin([padding,left_optimal_id]));
            padded_cond = egraph.add(SimpleLanguage::Ite([a,padded_left,right_optimal_id]))
        };



        let expr = egraph.id_to_expr(padded_cond);
        cost_model = RuntimeCostModel { egraph };
        let expr_cost = cost_model.cost_rec(&expr);
        println!("I constructed {} with cost {}\n",expr.to_string(),expr_cost);

        // Don't forget to union the new node with the matched node!
        if egraph.union(matched_id, padded_cond) {
            vec![padded_cond]
        } else {
            vec![]
        }
    }
}


impl Applier<SimpleLanguage, ()> for LoopStaticiser {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<SimpleLanguage, ()>,
        matched_id: Id, // Identifier of (let (?a ?b) ?c)
        subst: &Subst,
        _searcher_pattern: Option<&PatternAst<SimpleLanguage>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let a: Id = subst[self.label];
        let b: Id = subst[self.cond];
        let c: Id = subst[self.body];

        let label = egraph.id_to_expr(a).to_string();
        //println!("Label is {}",label);
        if label.starts_with("static") {
            return vec![];
        }

        let new_variable_index = UNIQUE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);

        let new_var = format!("static-i-{}-{}", new_variable_index,label);
        let variable_expr: RecExpr<SimpleLanguage> = new_var.parse().unwrap();
        
        let new_var = egraph.add_expr(&variable_expr);
        let inc_new_var = egraph.add(SimpleLanguage::Inc([new_var])); // (++ new-var)
        
        // (if original-condition old-body)
        // simplfied to ite or something like that
        let simplified_old_body:RecExpr<SimpleLanguage> = simplify_expr(egraph.id_to_expr(c)).parse().unwrap();
        let simplified_old_body_id = egraph.add_expr(&simplified_old_body);
        let temp = egraph.add(SimpleLanguage::If([b, simplified_old_body_id]));
        let condition  =  egraph.add_expr(&(simplify_expr(egraph.id_to_expr(temp))).parse().unwrap()); 

        
        // get max number of iterations
        let max_iterations = egraph.add(SimpleLanguage::Num(*ASSUMED_ITERATIONS.get(label.as_str()).unwrap())); 
        
        
        //setup the condition - new-var < max iterations
        let loop_condition = egraph.add(SimpleLanguage::Le([new_var,max_iterations])); 
        
        
        // (begin (if original-condiiton old-body) (++ new-var))
        let loop_body = egraph.add( SimpleLanguage::Begin([condition, inc_new_var]));
        
        
        // (while label (< new-var max-iterations) (begin...))
        let binding_body = egraph.add( SimpleLanguage::While([new_var, loop_condition ,loop_body])); 
        
        
        let zero = egraph.add(SimpleLanguage::Num(0));
        let new_expression = SimpleLanguage::Let([new_var, zero , binding_body]); // (let new-var 0 (while ...) )
        let new_expression_label = egraph.add(new_expression);

        println!("Converted {} to {}",egraph.id_to_expr(matched_id).to_string(),egraph.id_to_expr(new_expression_label).to_string());


        // Don't forget to union the new node with the matched node!
        if egraph.union(matched_id, new_expression_label) {
            vec![new_expression_label]
        } else {
            vec![]
        }
    }
}


fn make_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
    let mut ret: Vec<Rewrite<SimpleLanguage,()>> = vec![
        //rewrite!("add-0"; "(+ ?a 0)" <=> "?a"),
        //rewrite!("mul-1"; "(* ?a 1)" <=> "?a"),
        //rewrite!("neg-0"; "(- ?a 0)" <=> "?a"),
        //rewrite!("sum-2"; "(+ ?a ?a)" <=> "(* ?a 2)"),
        //rewrite!("mul-2"; "(* ?a ?a)" <=> "(** ?a 2)"),
        //rewrite!("neg-neg"; "(not (not ?a))" <=> "?a"),
        //rewrite!("inline-true"; "(not true)" <=> "false"),
        //rewrite!("inline-false"; "(not false)" <=> "true"),
        //rewrite!("swap-args-lt"; "(< ?a ?b)" <=> "(> ?b ?a)"),
        //rewrite!("swap-args-leq"; "(<= ?a ?b)" <=> "(>= ?b ?a)"),
        //rewrite!("while"; "(while ?x ?a ?b)" => "(ite ?a ?b (begin ?b (while (?x)-1 ?a ?b)))"),
        //rewrite!("inline-let-left"; "(let ?a ?b (?c ?d ?e))" <=> "(let ?a ?b (?c (let ?a ?b ?d) ?e))" ),
        //rewrite!("inline-let-right"; "(let ?a ?b (?c ?d ?e))" <=> "(let ?a ?b (?c ?d (let ?a ?b ?e))" ),
        //rewrite!("inline-let-collapse"; "(let ?a ?b (?c (let ?a ?b ?d) (let ?a ?b ?e)))" <=> "(?c (let ?a ?b ?e) (let ?a ?b ?d))" ),
        
        //rewrite!("neg-args-eq"; "(not (= ?a ?b))" <=> "(!= ?a ?b)"),
        //rewrite!("neg-args-neq"; "(not (!= ?a ?b))" <=> "(= ?a ?b)"),
        //rewrite!("filler-let"; "?a" <=> "(let UNUSED_VARIABLE 0 ?a)"),        
        rewrite!("not-not-true"; "(not true)" <=> "(not (not (not true)))"),
        rewrite!("not-true"; "true" <=> "(not (not true))"),
        rewrite!("filler-true-begin"; "?a" <=> "(begin true ?a)"),
        rewrite!("filler-false-begin"; "?a" <=> "(begin (not true) ?a)"),
        //rewrite!("ite-force"; "(ite ?a ?b ?c)" <=> "(ite-force ?a ?b ?c)"),
        //rewrite!("begin-swap" ;"(begin ?a (begin ?b ?c))" <=> "(begin ?b (begin ?a ?c))"),
        rewrite!("rewrite-ifs"; "(begin (if ?a ?b) (begin (if (not ?a) ?c) ?d))" <=> "(begin (ite ?a ?b ?c) ?d)"),
    ].into_iter().flatten().collect();

    let mut singletons = vec![
        rewrite!("staticise-while"; "(while ?a ?b ?c)" => { 
            //println!("STATICISE");
            LoopStaticiser {
                label: "?a".parse().unwrap(),
                cond: "?b".parse().unwrap(),
                body: "?c".parse().unwrap(),
            }} ),

        rewrite!("pad-if"; "(if ?a ?b)" => { 
            //println!("Pad-if");
            IFFiller {
            cond: "?a".parse().unwrap(),
            body: "?b".parse().unwrap()  
        }} 
        ),
        rewrite!("pad-ite"; "(ite ?a ?b ?c)" => {
            ITEFiller{
                cond: "?a".parse().unwrap(),
                left: "?b".parse().unwrap(),
                right: "?c".parse().unwrap(),
            }
        })
        //rewrite!("pad-padded-ite"; "(ite ?a ?b (not ?c))" => "(ite ?a ?b (not (not (not ?c))))"),
        // rewrite!("mul-0"; "(* ?a 0)" => "0"),
        // rewrite!("neg-eq"; "(- ?a ?a)" => "0"),
        // rewrite!("div-eq"; "(/ ?a ?a)" => "1"),
        // rewrite!("div-0"; "(/ 0 ?a)" => "0"),
        // rewrite!("args-eq-collapse"; "(= ?a ?a)" => "true"),
        // rewrite!("args-neq-collapse"; "(!= ?a ?a)" => "false"),
        // rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        // rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        // rewrite!("commute-eq"; "(= ?a ?b)" => "(= ?b ?a)"),
        // rewrite!("commute-neq"; "(!= ?a ?b)" => "(!= ?b ?a)"),
    ];

    ret.append(&mut singletons);

    ret
}

fn simplify_expr(expr: RecExpr<SimpleLanguage>) -> String{
    let runner = Runner::default()
    .with_explanations_enabled()
    .with_expr(&expr)
    .run(&make_rules());

// the Runner knows which e-class the expression given with `with_expr` is in
let root = runner.roots[0];
let calculator = RuntimeCostModel {
    egraph: &runner.egraph,
};

// use an Extractor to pick the best element of the root eclass
let extractor = Extractor::new(&runner.egraph, calculator);
    let (_, best) = extractor.find_best(root);
    best.to_string()
}


fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];
    let calculator = RuntimeCostModel {
        egraph: &runner.egraph,
    };

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, calculator);
    println!(
        "Starting cost is {:?}",
        RuntimeCostModel {
            egraph: &runner.egraph,
        }
        .cost_rec(&expr)
    );

    // for x in runner.egraph.classes() {
    //     println!("Class {:?}", x);
    //     for y in x.iter() {
    //         println!("Something {:?}", y)
    //     }
    // }

    let (best_cost, best) = extractor.find_best(root);
    println!(
        "Simplified {} to {} with final cost {}",
        expr, best, best_cost
    );
    best.to_string()
}

fn main() {
    //println!("{}", simplify("(while \n x true b)"));

    println!("{}",simplify(
        //"(let r (ite (apply (. x testBit) k) (apply (. (apply (apply standardMultiply s) y) mod) n) s)))"
//         "(while x (> e 0)
// (begin
//        (set! res (ite (apply odd? e)
//                       (let tmp (* s y)
//                                (mod (ite (> tmp m) (- tmp m) tmp)
//                                     m))
//                       s))
//        (apply halve e)))
//        "
    
    
"(let i 0 (while x (< i (. y bitLength)) (begin (if (apply (. y testBit) i) (set! ret (apply (. ret add) (apply (. x shiftLeft) i)))) (++ i))))")
    //)
);
        
    // "
    //(ite (not (apply (. exponent testBit) (- (- width i) 1))
    //        )
    //   (begin (set! r1 x) (begin (set! r0 x) goto))
    //   (begin (set! r0 y) (begin 0 (set! r1 y))))
    //"));
    //    "
    //"))
}
