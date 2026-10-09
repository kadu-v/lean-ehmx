use ehmx::core::{ClassPred, Constraint, Effect, Ty};
use ehmx::infer::{Output, Supply};
use ehmx::repl::Session;
use ehmx::solver::{solve, solve_with_fixed};
use std::collections::BTreeSet;

#[test]
fn eq_and_show_ground_instances_are_resolved() {
    let mut session = Session::with_solver(true);
    assert_eq!(
        session.process("eq 1 2").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true\nscheme: (Bool !{})"
    );
    session
        .process(":bind f : forall a. Show a => a -{}-> a")
        .unwrap();
    assert_eq!(
        session.process("f true").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true\nscheme: (Bool !{})"
    );
    assert_eq!(
        session.process("f 1").unwrap(),
        "type: Int\neffect: {}\nconstraints: true\nscheme: (Int !{})"
    );
}

#[test]
fn unresolved_class_predicate_stays_in_output() {
    let mut session = Session::with_solver(true);
    let output = session.process(r"\x -> eq x x").unwrap();
    assert!(output.contains("type: (α"));
    assert!(output.contains("effect: {}"));
    assert!(output.contains("constraints: Eq α"));
    assert!(output.contains("scheme: ∀α"));
    assert!(output.contains(". Eq α"));
    assert!(output.contains("=> ((α"));
    assert!(output.contains("-{}-> Bool) !{})"));
}

#[test]
fn unsupported_instance_is_rejected_unless_assumed() {
    let mut session = Session::with_solver(true);
    session
        .process(":bind f : Show (Int -{}-> Int) => Int")
        .unwrap();
    assert!(session.process("f").unwrap_err().contains("NoInstance"));
    session.process(":assume Show (Int -{}-> Int)").unwrap();
    assert_eq!(
        session.process("f").unwrap(),
        "type: Int\neffect: {}\nconstraints: true\nscheme: (Int !{})"
    );
}

#[test]
fn solver_keeps_quantified_handler_constraints_and_mode_after_reset() {
    let mut session = Session::with_solver(true);
    assert_eq!(
        session.process("perform ping 1").unwrap(),
        "type: Int\neffect: {ping}\nconstraints: true\nscheme: (Int !{ping})"
    );
    let output = session
        .process("handle (perform ping 1) with { return r -> r; ping(x;k) -> k x }")
        .unwrap();
    assert_eq!(
        output,
        "type: Int\neffect: {μ6}\nconstraints: true\nscheme: ∀μ6. (Int !{μ6})"
    );
    session.process(":reset").unwrap();
    assert_eq!(
        session.process("eq true false").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true\nscheme: (Bool !{})"
    );
}

#[test]
fn let_bound_handler_constraints_and_equal_effects_simplify() {
    let mut session = Session::with_solver(true);
    let output = session
        .process(r"let a = \x -> handle (perform ping x) with { return r -> r; ping(x;k) -> k x } in a 1")
        .unwrap();
    assert_eq!(
        output,
        "type: Int\neffect: {μ25}\nconstraints: true\nscheme: ∀μ25. (Int !{μ25})"
    );
}

#[test]
fn environment_names_are_not_solved_away() {
    let mut session = Session::with_solver(true);
    session.process(":bind x : a").unwrap();
    let output = session.process("x 1").unwrap();
    assert!(output.contains("constraints: α"));
    assert!(!output.contains("constraints: true"));

    let equal_effects = Constraint::and(
        Constraint::EffectLe(Effect::var(0), Effect::var(1)),
        Constraint::EffectLe(Effect::var(1), Effect::var(0)),
    );
    let output = Output {
        ty: Ty::Var(0),
        effect: Effect::var(1),
        constraints: equal_effects.clone(),
        next: Supply::default(),
    };
    let solved =
        solve_with_fixed(output, &[], &BTreeSet::from([0]), &BTreeSet::from([0, 1])).unwrap();
    assert_eq!(solved.constraints, equal_effects);
    assert_eq!(solved.effect, Effect::var(1));
}

#[test]
fn existential_witness_must_respect_quantifier_order() {
    let output = |constraints| Output {
        ty: Ty::Base(ehmx::core::BaseTy::Int),
        effect: Effect::default(),
        constraints,
        next: Supply::default(),
    };
    let inner_existential = Constraint::AllTy(
        0,
        Box::new(Constraint::ExTy(
            1,
            Box::new(Constraint::TypeEq(Ty::Var(1), Ty::Var(0))),
        )),
    );
    assert_eq!(
        solve(output(inner_existential), &[] as &[ClassPred])
            .unwrap()
            .constraints,
        Constraint::Top
    );

    let outer_existential = Constraint::ExTy(
        1,
        Box::new(Constraint::AllTy(
            0,
            Box::new(Constraint::TypeEq(Ty::Var(1), Ty::Var(0))),
        )),
    );
    assert_eq!(
        solve(output(outer_existential.clone()), &[] as &[ClassPred])
            .unwrap()
            .constraints,
        outer_existential
    );

    let same_effects = Constraint::and(
        Constraint::EffectLe(Effect::var(1), Effect::var(0)),
        Constraint::EffectLe(Effect::var(0), Effect::var(1)),
    );
    let inner_existential = Constraint::AllEff(
        0,
        Box::new(Constraint::ExEff(1, Box::new(same_effects.clone()))),
    );
    assert_eq!(
        solve(output(inner_existential), &[] as &[ClassPred])
            .unwrap()
            .constraints,
        Constraint::Top
    );
    let outer_existential =
        Constraint::ExEff(1, Box::new(Constraint::AllEff(0, Box::new(same_effects))));
    assert_eq!(
        solve(output(outer_existential.clone()), &[] as &[ClassPred])
            .unwrap()
            .constraints,
        outer_existential
    );
}

#[test]
fn generalization_respects_free_environment_names() {
    let mut session = Session::with_solver(true);
    session.process(":bind x : a").unwrap();
    let output = session.process("x").unwrap();
    assert!(output.contains("scheme: (α"));
    assert!(!output.contains("scheme: ∀"));

    session
        .process(":bind f : forall a ?e. a -{?e}-> a")
        .unwrap();
    let output = session.process("f").unwrap();
    assert!(output.contains("scheme: ∀α"));
    assert!(output.contains(" μ"));
}

#[test]
fn a_lack_on_one_tail_does_not_empty_another_tail() {
    let c = Constraint::and(
        Constraint::EffectLe(Effect::var(0).union(&Effect::var(1)), Effect::singleton(0)),
        Constraint::Lacks(0, Effect::var(0)),
    );
    let output = Output {
        ty: Ty::Var(0),
        effect: Effect::var(1),
        constraints: c,
        next: Supply::default(),
    };
    let solved = solve(output, &[] as &[ClassPred]).unwrap();
    assert_eq!(solved.effect, Effect::var(1));
    assert_eq!(
        solved.constraints,
        Constraint::EffectLe(Effect::var(1), Effect::singleton(0))
    );
}
