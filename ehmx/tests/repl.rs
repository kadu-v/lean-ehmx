use ehmx::repl::Session;

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
fn operation_and_handler_keep_symbolic_effect() {
    let mut s = Session::new();
    s.process(":op ping : forall a. a -> a").unwrap();
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
    assert!(s.process(":op ping : a -> a").is_err());
    assert_eq!(s.process(":env").unwrap(), "empty environment");
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
    s.process(":op ping : forall a. a -> a").unwrap();
    assert!(
        s.process("handle (perform ping x) with { return r -> r; ping(v;v) -> v }")
            .is_err()
    );
}
