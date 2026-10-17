import EHMX

/-! Exact Goal-type checks for completed obligations. PreservationGoal,
OperationPreservationGoal and the two reachability safety goals remain unproved;
no assumption of those propositions is used to make this test pass. -/
example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.ProgressGoal S M sig := EHMX.progressEffectSafety S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.SchemeValueSubstitutionGoal S M sig := EHMX.schemeValueSubstitution S M sig
