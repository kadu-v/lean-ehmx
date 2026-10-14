import EHMX.HMX.GroundTyping

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

def Inference.Protected (X : Constraints T O) (g : Context X) (t : T.Term) (eff : Effect) : Names :=
  (g.support.union (T.support t)).union ⟨∅, eff.vars⟩

def Scheme.generalize {X : Constraints T O} (g : Context X) (c : X.Formula)
    (t : T.Term) : Scheme X := .qualified (g.generalizationNames c t) c t

/-- Structural constraint generation. No typing oracle or choice of a derivation
is used. `none` denotes a missing variable or operation. Constraint consistency is
left to the solver. Signature closure is a premise of correctness. -/
def generate (sig : Signature T) (X : Constraints T O) (N : X.Simplifier) :
    Expr → Context X → T.Term → Effect → Names → Option X.Formula
  | .var i, g, t, eff, fixed =>
      (g[i]?).map (fun s => X.instantiateConstraint X.top s t eff (fixed.union (X.support X.top)))
  | .int _, _, t, eff, _ => some (X.checked X.top X.top (T.literal .int) t ∅ eff)
  | .bool _, _, t, eff, _ => some (X.checked X.top X.top (T.literal .bool) t ∅ eff)
  | .lam body, g, t, eff, fixed => do
      let a := T.var (fixed.shiftTypes 0)
      let b := T.var (fixed.shiftTypes 1)
      let latent := Effect.var (fixed.shiftEffects 0)
      let cg := .mono a :: g
      let locals : Names := ⟨{fixed.shiftTypes 0, fixed.shiftTypes 1}, {fixed.shiftEffects 0}⟩
      let cf := fixed.union ((Inference.Protected X cg b latent).union locals)
      let d ← generate sig X N body cg b latent cf
      pure (X.checked X.top d (T.arrow a latent b) t ∅ eff)
  | .app f x, g, t, eff, fixed => do
      let ft := T.var (fixed.shiftTypes 0)
      let xt := T.var (fixed.shiftTypes 1)
      let ef := Effect.var (fixed.shiftEffects 0)
      let ex := Effect.var (fixed.shiftEffects 1)
      let latent := Effect.var (fixed.shiftEffects 2)
      let both := fixed.union ((Inference.Protected X g ft ef).union
        ((Inference.Protected X g xt ex).union ⟨∅, latent.vars⟩))
      let df ← generate sig X N f g ft ef both
      let dx ← generate sig X N x g xt ex (both.union (X.support df))
      pure (X.conjunction [X.top, df, dx, X.le ft (T.arrow xt latent t),
        X.effectEq (ef ∪ ex ∪ latent) eff])
  | .letE val body, g, t, eff, fixed => do
      let a := T.var (fixed.shiftTypes 0)
      if Value.isValue val then
        let dv ← generate sig X N val g a ∅ (fixed.union (Inference.Protected X g a ∅))
        let s := Scheme.generalize g (N.run dv) a
        let projected := X.existsNames (g.generalizationNames (N.run dv) a) (N.run dv)
        let bf := fixed.union ((Inference.Protected X (s :: g) t eff).union (X.support projected))
        let db ← generate sig X N body (s :: g) t eff bf
        pure (X.conjunction [X.top, projected, db])
      else
        let ev := Effect.var (fixed.shiftEffects 0)
        let eb := Effect.var (fixed.shiftEffects 1)
        let cg := .mono a :: g
        let both := fixed.union ((Inference.Protected X g a ev).union (Inference.Protected X cg t eb))
        let dv ← generate sig X N val g a ev both
        let db ← generate sig X N body cg t eb (both.union (X.support dv))
        pure (X.conjunction [X.top, dv, db, X.effectEq (ev ∪ eb) eff])
  | .perform op arg, g, t, eff, fixed => do
      let raw ← sig op
      let sub := Substitution.freshen T raw.bound fixed.shiftTypes fixed.shiftEffects
      let tin := sub.apply raw.input
      let tout := sub.apply raw.output
      let keep := fixed.union ((T.support tin).union (T.support tout))
      let ea := Effect.var (keep.shiftEffects 0)
      let d ← generate sig X N arg g tin ea (keep.union (Inference.Protected X g tin ea))
      pure (X.checked X.top (X.and d (X.le tin tin)) tout t (Effect.singleton op ∪ ea) eff)
  | .handle body op ret clause, g, target, out, fixed => do
      let raw ← sig op
      let input := T.var (fixed.shiftTypes 0)
      let result := T.var (fixed.shiftTypes 1)
      let ein := Effect.var (fixed.shiftEffects 0)
      let er := Effect.var (fixed.shiftEffects 1)
      let rest := Effect.var (fixed.shiftEffects 2)
      let core := fixed.union ((T.support input).union ((T.support result).union
        ⟨∅, ein.vars ∪ er.vars ∪ rest.vars⟩))
      let db ← generate sig X N body g input ein core
      let rf := core.union (X.support db)
      let dr ← generate sig X N ret (.mono input :: g) result er rf
      let outer := rf.union (X.support dr)
      let decl := raw.rename outer.shiftTypes outer.shiftEffects
      let cg := .mono (T.arrow decl.output out result) :: .mono decl.input :: g
      let cf := outer.union ((Inference.Protected X cg result out).union
        (((T.support decl.input).union (T.support decl.output)).union decl.bound))
      let eo := Effect.var (cf.shiftEffects 0)
      let dc ← generate sig X N clause cg result eo (cf.union (Inference.Protected X cg result eo))
      let hidden := ((X.support dc).union ⟨∅, eo.vars⟩).diff cf
      let d := X.handler X.top db dr dc decl op result result result ein er eo rest out hidden
      pure (X.checked X.top d result target out out)

/-- Hide exactly the generated names outside the observable context and result. -/
def generateProjected (sig : Signature T) (X : Constraints T O) (N : X.Simplifier)
    (g : Context X) (e : Expr) (t : T.Term) (eff : Effect) : Option X.Formula :=
  let fixed := (Inference.Protected X g t eff).union (X.support X.top)
  (generate sig X N e g t eff fixed).map (fun d => X.existsNames ((X.support d).diff fixed) d)

end EHMX.HMX
