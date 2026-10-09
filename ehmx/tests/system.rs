use ehmx::core::{Constraint, Effect, EmptyPred, Expr, OpDecl, Ty};
use ehmx::infer::Supply;
use ehmx::system::{PredicateSystem, QualifiedScheme, generate};
use std::collections::{BTreeMap, BTreeSet};

#[test]
fn empty_domain_generates_a_handler_constraint() {
    let x = PredicateSystem::<EmptyPred>::new();
    let mut sig = BTreeMap::new();
    sig.insert(
        0,
        OpDecl {
            type_vars: [0].into(),
            effect_vars: BTreeSet::new(),
            input: Ty::Var(0),
            output: Ty::Var(0),
        },
    );
    let body = Expr::Perform(0, Box::new(Expr::Int("1".into())));
    let ret = Expr::Var(0);
    let clause = Expr::App(Box::new(Expr::Var(0)), Box::new(Expr::Var(1)));
    let e = Expr::Handle(Box::new(body), 0, Box::new(ret), Box::new(clause));
    let r = generate(&x, &sig, &[], &e, Supply::default()).unwrap();
    assert!(matches!(r.ty, Ty::Var(_)));
    let generated = format!("{:?}", r.condition);
    assert!(generated.contains("AllTy"));
    assert!(generated.contains("ExTy"));
    assert!(generated.contains("Lacks(0"));
}

#[test]
fn class_formulas_are_whole_conditions_in_generic_scheme() {
    use ehmx::core::ClassPred;
    let x = PredicateSystem::<ClassPred>::new();
    let scheme = QualifiedScheme {
        type_vars: [0].into(),
        effect_vars: BTreeSet::new(),
        condition: Constraint::and(
            Constraint::Pred(ClassPred::Eq(Ty::Var(0))),
            Constraint::EffectLe(Effect::default(), Effect::default()),
        ),
        result: Ty::Var(0),
    };
    let r = generate(
        &x,
        &BTreeMap::new(),
        &[scheme],
        &Expr::Var(0),
        Supply {
            types: 2,
            effects: 0,
        },
    )
    .unwrap();
    assert_eq!(r.ty, Ty::Var(3));
    assert!(format!("{:?}", r.condition).contains("Eq(Var(3))"));
}
