use ehmx::core::{ClassPred, Constraint, Effect, Expr, OpDecl, Scheme, Ty};
use ehmx::infer::{InferError, Supply, generate, infer_qualified, infer_symbolic};
use ehmx::repl::Session;
use std::collections::{BTreeMap, BTreeSet};

#[test]
fn literals_and_type_mismatch() {
    let mut s = Session::new();
    assert_eq!(
        s.process("true").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true"
    );
    assert_eq!(
        s.process("-00042").unwrap(),
        "type: Int\neffect: {}\nconstraints: true"
    );
    assert!(s.process("1 true").unwrap_err().contains("TypeMismatch"));
    assert_eq!(
        s.process("123456789012345678901234567890").unwrap(),
        "type: Int\neffect: {}\nconstraints: true"
    );
}

#[test]
fn application_keeps_unification_constraints() {
    let mut s = Session::new();
    let output = s.process(r"(\x -> x) 1").unwrap();
    assert!(output.contains("type: α"));
    assert!(output.contains("effect: {μ"));
    assert!(output.contains("= Int"));
    assert!(output.contains("⊆ {}"));
}

#[test]
fn qualified_value_let_and_exact_assumption() {
    let mut s = Session::new();
    s.process(":bind f : forall a. Eq a => a -{}-> a").unwrap();
    let output = s.process("f 1").unwrap();
    assert!(output.contains("Eq α"));
    assert!(output.contains("= Int"));
    s.process(":bind g : Eq Int => Int -{}-> Int").unwrap();
    s.process(":assume Eq Int").unwrap();
    let output = s.process("g 1").unwrap();
    assert_eq!(output.matches("Eq Int").count(), 1);
    let output = s.process(r"let id = \x -> x in id true").unwrap();
    assert!(output.contains("= Bool"));
}

#[test]
fn value_let_keeps_its_residual_constraint() {
    let mut s = Session::new();
    s.process(":bind f : Eq Int => Int").unwrap();
    let output = s.process("let x = f in 1").unwrap();
    assert!(output.contains("type: Int"));
    assert!(output.contains("constraints: Eq Int"));
}

#[test]
fn qualified_inference_avoids_context_name_collision() {
    let ctx: Vec<Scheme<ClassPred>> = vec![Scheme::mono(Ty::Var(0))];
    let sig = BTreeMap::new();
    let e = Expr::Lam(Box::new(Expr::Var(1)));
    let r = infer_qualified(&sig, &ctx, &e, Supply::default(), &[]).unwrap();
    assert_eq!(
        r.ty,
        Ty::Arr(
            Box::new(Ty::Var(1)),
            Effect::default(),
            Box::new(Ty::Var(0))
        )
    );
}

#[test]
fn symbolic_inference_keeps_inconsistent_constraints() {
    let sig = BTreeMap::new();
    let e = Expr::App(Box::new(Expr::Int("1".into())), Box::new(Expr::Bool(true)));
    let symbolic = infer_symbolic::<ClassPred>(&sig, &[], &e, Supply::default(), &[]).unwrap();
    assert!(format!("{:?}", symbolic.constraints).contains("TypeEq"));
    assert!(infer_qualified::<ClassPred>(&sig, &[], &e, Supply::default(), &[]).is_err());
}

#[test]
fn operation_and_handler_keep_symbolic_effect() {
    let mut s = Session::new();
    s.process(":bind y : Int").unwrap();
    let output = s.process("perform ping y").unwrap();
    assert!(output.contains("effect: {ping}"));
    let output = s
        .process("handle (perform ping y) with { return r -> r; ping(x;k) -> k x }")
        .unwrap();
    assert!(output.contains("effect: {μ"));
    assert!(output.contains("ping ∉"));
    assert!(output.contains("∀α"));
}

#[test]
fn failed_declaration_does_not_change_environment() {
    let mut s = Session::new();
    assert!(s.process(":op pong : a -> a").is_err());
    assert!(s.process(":env").unwrap().contains("eq: ∀α1. Eq α1 =>"));
    assert!(
        s.process("missing")
            .unwrap_err()
            .contains("unbound variable")
    );
}

#[test]
fn effect_polymorphic_scheme_and_binder_errors() {
    let mut s = Session::new();
    s.process(":bind h : forall a ?e. a -{?e}-> a").unwrap();
    s.process(":bind x : Int").unwrap();
    let out = s.process("h x").unwrap();
    assert!(out.contains("effect: {μ"));
    assert!(out.contains("= Int"));
    assert!(
        s.process("handle (perform ping x) with { return r -> r; ping(v;v) -> v }")
            .is_err()
    );
}

#[test]
fn ping_is_builtin_and_restored_by_reset() {
    let mut s = Session::new();
    assert!(
        s.process("perform ping 1")
            .unwrap()
            .contains("effect: {ping}")
    );
    assert!(
        s.process(":op ping : forall a. a -> a")
            .unwrap_err()
            .contains("already declared")
    );
    s.process(":reset").unwrap();
    assert!(s.process(":env").unwrap().contains("eq: ∀α1. Eq α1 =>"));
    assert!(
        s.process("perform ping true")
            .unwrap()
            .contains("effect: {ping}")
    );
}

#[test]
fn eq_is_available_at_startup_and_after_reset() {
    let mut s = Session::new();
    let env = s.process(":env").unwrap();
    assert!(env.contains("eq: ∀α1. Eq α1 =>"));
    assert!(env.contains("Bool"));
    let out = s.process("eq 1 2").unwrap();
    assert!(out.contains("Eq α"));
    assert!(out.contains("= Int"));
    s.process(":reset").unwrap();
    let out = s.process("eq true false").unwrap();
    assert!(out.contains("Eq α"));
    assert!(out.contains("= Bool"));
}

#[test]
fn polymorphic_ping_clause_cannot_return_its_argument() {
    let mut s = Session::new();
    let invalid =
        r"handle (let x = \x -> x in perform ping x) with { return r -> r; ping(x;k) -> x }";
    assert!(
        s.process(invalid)
            .unwrap_err()
            .contains("RigidTypeMismatch")
    );
    let valid =
        r"handle (let x = \x -> x in perform ping x) with { return r -> r; ping(x;k) -> k x }";
    assert!(s.process(valid).unwrap().contains("effect: {μ"));
}

#[test]
fn handler_clause_instantiates_polymorphic_id_per_operation_type() {
    let mut s = Session::new();
    s.process(":bind id : forall a. a -{}-> a").unwrap();
    let output = s
        .process(r"\y -> handle (perform ping y) with { return r -> r; ping(x;k) -> k (id x) }")
        .unwrap();
    assert!(output.contains("∀α"));
    assert!(output.contains("∃α"));
    assert!(output.contains("effect: {}"));
}

#[test]
fn handler_alpha_renames_operation_binder_away_from_context() {
    let mut sig = BTreeMap::new();
    sig.insert(
        0,
        OpDecl {
            type_vars: BTreeSet::from([0]),
            effect_vars: BTreeSet::new(),
            input: Ty::Var(0),
            output: Ty::Var(0),
        },
    );
    let ctx: Vec<Scheme<ClassPred>> = vec![Scheme::mono(Ty::Var(0))];
    let expr = Expr::Handle(
        Box::new(Expr::Perform(0, Box::new(Expr::Var(0)))),
        0,
        Box::new(Expr::Var(0)),
        Box::new(Expr::App(Box::new(Expr::Var(0)), Box::new(Expr::Var(1)))),
    );
    assert!(
        generate(
            &sig,
            &ctx,
            &expr,
            Supply {
                types: 2,
                effects: 1
            }
        )
        .is_ok()
    );
}

#[test]
fn scheme_instantiation_avoids_free_and_inner_bound_names() {
    let sig = BTreeMap::new();
    let free: Scheme<ClassPred> = Scheme {
        type_vars: BTreeSet::from([0]),
        effect_vars: BTreeSet::new(),
        predicates: Constraint::TypeEq(Ty::Var(0), Ty::Var(1)),
        result: Ty::Var(0),
    };
    let inner: Scheme<ClassPred> = Scheme {
        type_vars: BTreeSet::from([0]),
        effect_vars: BTreeSet::new(),
        predicates: Constraint::AllTy(1, Box::new(Constraint::TypeEq(Ty::Var(0), Ty::Var(1)))),
        result: Ty::Var(0),
    };
    for scheme in [free, inner] {
        assert!(matches!(
            generate(
                &sig,
                &[scheme.clone()],
                &Expr::Var(0),
                Supply {
                    types: 0,
                    effects: 0
                }
            ),
            Err(InferError::SchemeCapture)
        ));
        assert!(
            generate(
                &sig,
                &[scheme],
                &Expr::Var(0),
                Supply {
                    types: 2,
                    effects: 0
                }
            )
            .is_ok()
        );
    }
}
