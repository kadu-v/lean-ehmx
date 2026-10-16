import EHMX.HMX.Declarative

namespace EHMX.HMX
variable {T : TypeSyntax}

def Inference.Protected (X : Theory T) (g : Context X) (t : T.Term) (eff : Effect) : Names :=
  (g.support.union (T.support t)).union ⟨∅, eff.vars⟩

namespace Theory
variable (X : Theory T)

/-- Variable, literal and abstraction rules introduce an equality, as in
Figure 4.4. Application retains the logical type-comparison predicate. -/
def checked (input output : X.Formula) (actual expected : T.Term)
    (effect expectedEffect : Effect) : X.Formula :=
  X.conjunction [input, output, X.eq actual expected, X.effectEq effect expectedEffect]

def instantiateConstraint (c : X.Formula) (s : Scheme X)
    (expected : T.Term) (eff : Effect) (fixed : Names) : X.Formula :=
  match s with
  | .mono t => X.checked c X.top t expected ∅ eff
  | .qualified a d t =>
      let avoid := fixed.union s.support
      let θ := FiniteSubstitution.freshen T a avoid.shiftTypes avoid.shiftEffects
      X.existsNames (a.freshImage avoid)
        (X.checked c (X.subst θ d) (θ.apply t) expected ∅ eff)

def handler (c db dr dc : X.Formula) (decl : Operation T) (op : Op)
    (tr tc result : T.Term) (ein er eo rest out : Effect) (witnesses : Names) : X.Formula :=
  X.conjunction [c, db, dr, X.le tr result,
    X.clause decl.bound witnesses (X.and dc (X.and (X.le tc result) (X.effectLe eo out))),
    X.split op ein rest, X.effectLe rest out, X.effectLe er out]
end Theory

/-- Structural constraint generation. No typing oracle or choice of a derivation
is used. `none` denotes a missing variable or operation. Constraint consistency is
left to the solver. Signature closure is a premise of correctness. -/
noncomputable def generate (sig : Signature T) (X : Theory T) (N : X.Simplifier) :
    Expr → Context X → Nat → Effect → Names → Option X.Formula
  | .var i, g, resultName, eff, fixed =>
      let t := T.var resultName
      (g.locals[i]?).map (fun s => X.instantiateConstraint X.top s t eff (fixed.union (X.support X.top)))
  | .const k, g, resultName, eff, fixed =>
      let t := T.var resultName
      (g.lookupConstant k).map (fun s => X.instantiateConstraint X.top s t eff fixed)
  | .lam body, g, resultName, eff, fixed => do
      let t := T.var resultName
      let a := T.var (fixed.shiftTypes 0)
      let b := T.var (fixed.shiftTypes 1)
      let latent := Effect.var (fixed.shiftEffects 0)
      let cg := g.extend (.mono a)
      let locals : Names := ⟨{fixed.shiftTypes 0, fixed.shiftTypes 1}, {fixed.shiftEffects 0}⟩
      let cf := fixed.union ((Inference.Protected X cg b latent).union locals)
      let d ← generate sig X N body cg (fixed.shiftTypes 1) latent cf
      pure (X.existsNames locals (X.checked X.top d (T.arrow a latent b) t ∅ eff))
  | .app f x, g, resultName, eff, fixed => do
      let t := T.var resultName
      let ft := T.var (fixed.shiftTypes 0)
      let xt := T.var (fixed.shiftTypes 1)
      let ef := Effect.var (fixed.shiftEffects 0)
      let ex := Effect.var (fixed.shiftEffects 1)
      let latent := Effect.var (fixed.shiftEffects 2)
      let both := fixed.union ((Inference.Protected X g ft ef).union
        ((Inference.Protected X g xt ex).union ⟨∅, latent.vars⟩))
      let df ← generate sig X N f g (fixed.shiftTypes 0) ef both
      let dx ← generate sig X N x g (fixed.shiftTypes 1) ex (both.union (X.support df))
      pure (X.existsNames ⟨{fixed.shiftTypes 0, fixed.shiftTypes 1},
        {fixed.shiftEffects 0, fixed.shiftEffects 1, fixed.shiftEffects 2}⟩
        (X.conjunction [X.top, df, dx, X.le ft (T.arrow xt latent t),
          X.effectEq (ef ∪ ex ∪ latent) eff]))
  | .letE val body, g, resultName, eff, fixed => do
      let t := T.var resultName
      let a := T.var (fixed.shiftTypes 0)
      if Value.isValue val then
        let dv ← generate sig X N val g (fixed.shiftTypes 0) ∅ (fixed.union (Inference.Protected X g a ∅))
        let bound : Names := ⟨{fixed.shiftTypes 0}, ∅⟩
        let s := Scheme.qualified bound (N.run dv) a
        let projected := X.existsNames bound (N.run dv)
        let bf := fixed.union ((Inference.Protected X (g.extend s) t eff).union (X.support projected))
        let db ← generate sig X N body (g.extend s) resultName eff bf
        pure (X.conjunction [X.top, projected, db])
      else
        let ev := Effect.var (fixed.shiftEffects 0)
        let eb := Effect.var (fixed.shiftEffects 1)
        let cg := g.extend (.mono a)
        let both := fixed.union ((Inference.Protected X g a ev).union (Inference.Protected X cg t eb))
        let dv ← generate sig X N val g (fixed.shiftTypes 0) ev both
        let db ← generate sig X N body cg resultName eb (both.union (X.support dv))
        pure (X.existsNames ⟨{fixed.shiftTypes 0}, {fixed.shiftEffects 0, fixed.shiftEffects 1}⟩
          (X.conjunction [X.top, dv, db, X.effectEq (ev ∪ eb) eff]))
  | .perform op arg, g, resultName, eff, fixed => do
      let t := T.var resultName
      let raw ← sig op
      let sub := FiniteSubstitution.freshen T raw.bound fixed.shiftTypes fixed.shiftEffects
      let tin := sub.apply raw.input
      let tout := sub.apply raw.output
      let keep := fixed.union (((T.support tin).union (T.support tout)).union (raw.bound.freshImage fixed))
      let argTy := T.var (keep.shiftTypes 0)
      let ea := Effect.var (keep.shiftEffects 0)
      let d ← generate sig X N arg g (keep.shiftTypes 0) ea (keep.union (Inference.Protected X g argTy ea))
      let hidden := (raw.bound.freshImage fixed).union ⟨{keep.shiftTypes 0}, {keep.shiftEffects 0}⟩
      pure (X.existsNames hidden (X.checked X.top (X.and d (X.le argTy tin))
        tout t (Effect.singleton op ∪ ea) eff))
  | .handle body op ret clause, g, resultName, out, fixed => do
      let target := T.var resultName
      let raw ← sig op
      let input := T.var (fixed.shiftTypes 0)
      let result := T.var (fixed.shiftTypes 1)
      let retTy := T.var (fixed.shiftTypes 2)
      let ein := Effect.var (fixed.shiftEffects 0)
      let er := Effect.var (fixed.shiftEffects 1)
      let rest := Effect.var (fixed.shiftEffects 2)
      let core := fixed.union ((T.support input).union ((T.support result).union ((T.support retTy).union
        ⟨∅, ein.vars ∪ er.vars ∪ rest.vars⟩)))
      let db ← generate sig X N body g (fixed.shiftTypes 0) ein core
      let rf := core.union (X.support db)
      let dr ← generate sig X N ret (g.extend (.mono input)) (fixed.shiftTypes 2) er rf
      let outer := rf.union (X.support dr)
      let decl := raw.rename outer.shiftTypes outer.shiftEffects
      let cg := (g.extend (.mono decl.input)).extend (.mono (T.arrow decl.output out result))
      let cf := outer.union ((Inference.Protected X cg result out).union
        (((T.support decl.input).union (T.support decl.output)).union decl.bound))
      let clauseTy := T.var (cf.shiftTypes 0)
      let eo := Effect.var (cf.shiftEffects 0)
      let dc ← generate sig X N clause cg (cf.shiftTypes 0) eo (cf.union (Inference.Protected X cg clauseTy eo))
      let hidden : Names := ⟨{cf.shiftTypes 0}, {cf.shiftEffects 0}⟩
      let d := X.handler X.top db dr dc decl op retTy clauseTy result ein er eo rest out hidden
      pure (X.existsNames ⟨{fixed.shiftTypes 0, fixed.shiftTypes 1, fixed.shiftTypes 2},
        {fixed.shiftEffects 0, fixed.shiftEffects 1, fixed.shiftEffects 2}⟩
        (X.checked X.top d result target out out))

/-- Hide exactly the generated names outside the observable context and result. -/
noncomputable def generateProjected (sig : Signature T) (X : Theory T) (N : X.Simplifier)
    (g : Context X) (e : Expr) (resultName : Nat) (eff : Effect) : Option X.Formula :=
  let t := T.var resultName
  let fixed := (Inference.Protected X g t eff).union (X.support X.top)
  (generate sig X N e g resultName eff fixed).map (fun d => X.existsNames ((X.freeNames d).diff ((g.freeNames.union (T.support t)).union ⟨∅, eff.vars⟩)) d)

end EHMX.HMX
