use ehmx::core::{ClassPred, Constraint, Effect, Ty};
use ehmx::infer::{Output, Supply};
use ehmx::repl::Session;
use ehmx::solver::solve;

#[test]
fn eq_and_show_ground_instances_are_resolved() {
    let mut session = Session::with_solver(true);
    assert_eq!(
        session.process("eq 1 2").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true"
    );
    session
        .process(":bind f : forall a. Show a => a -{}-> a")
        .unwrap();
    assert_eq!(
        session.process("f true").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true"
    );
    assert_eq!(
        session.process("f 1").unwrap(),
        "type: Int\neffect: {}\nconstraints: true"
    );
}

#[test]
fn unresolved_class_predicate_stays_in_output() {
    let mut session = Session::with_solver(true);
    let output = session.process(r"\x -> eq x x").unwrap();
    assert!(output.contains("type: (α"));
    assert!(output.contains("effect: {}"));
    assert!(output.contains("constraints: Eq α"));
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
        "type: Int\neffect: {}\nconstraints: true"
    );
}

#[test]
fn solver_keeps_quantified_handler_constraints_and_mode_after_reset() {
    let mut session = Session::with_solver(true);
    assert_eq!(
        session.process("perform ping 1").unwrap(),
        "type: Int\neffect: {ping}\nconstraints: true"
    );
    let output = session
        .process("handle (perform ping 1) with { return r -> r; ping(x;k) -> k x }")
        .unwrap();
    assert!(output.contains("type: Int"));
    assert!(output.contains("effect: {μ"));
    assert!(output.contains("∀α"));
    assert!(!output.contains("ping ∉"));
    session.process(":reset").unwrap();
    assert_eq!(
        session.process("eq true false").unwrap(),
        "type: Bool\neffect: {}\nconstraints: true"
    );
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
