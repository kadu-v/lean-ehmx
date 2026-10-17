import HMX.LocallyNameless.Syntax
import HMX.Semantics

namespace HMX.LN

/-- Total stacks allow evaluation of raw syntax; WF excludes out-of-scope reads. -/
def push {α : Type} (vs : List α) (σ : Nat → α) (i : Nat) : α :=
  (vs[i]?).getD (σ (i - vs.length))

def Ty.evalAt (M : Model) (ρ : Assignment M) (β : Nat → M.Carrier) : Ty → M.Carrier
  | .free X => ρ X
  | .bound i => β i
  | .con f ts => M.constructor f (ts.map (Ty.evalAt M ρ β))

def Ty.eval (M : Model) (ρ : Assignment M) (T : Ty) : M.Carrier :=
  T.evalAt M ρ (fun _ => ρ (0,0))

mutual
def Constraint.holdsAt (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) : Constraint → Prop
  | .truth => True
  | .falsity => False
  | .atom p ts => p.eval M (ts.map (Ty.evalAt M ρ β))
  | .conj C D => C.holdsAt S M ρ ι β γ ∧ D.holdsAt S M ρ ι β γ
  | .exists_ ks C => ∃ vs, List.Forall₂ (fun v k => M.kind v = k) vs ks ∧
      C.holdsAt S M ρ ι (push vs β) γ
  | .def_ _ s C => C.holdsAt S M ρ ι β (push [s.denoteAt S M ρ ι β γ] γ)
  | .inst (.free x) T => T.evalAt M ρ β ∈ ι x
  | .inst (.bound i) T => T.evalAt M ρ β ∈ γ i
def Scheme.denoteAt (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) : Scheme → Set M.Carrier
  | .all ks C T => {v | M.kind v = 0 ∧ ∃ vs,
      List.Forall₂ (fun w k => M.kind w = k) vs ks ∧
      C.holdsAt S M ρ ι (push vs β) γ ∧ M.below 0 (T.evalAt M ρ (push vs β)) v}
end

def Constraint.Holds (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) (C : Constraint) : Prop :=
  C.holdsAt S M ρ ι (fun _ => ρ (0,0)) (fun _ => ∅)

def Scheme.denote (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) (s : Scheme) : Set M.Carrier :=
  s.denoteAt S M ρ ι (fun _ => ρ (0,0)) (fun _ => ∅)

def Entails (S : Signature) (M : Model) (C D : Constraint) : Prop :=
  ∀ ρ ι, ρ.Valid S M → ι.Valid M → C.Holds S M ρ ι → D.Holds S M ρ ι

def Equivalent (S : Signature) (M : Model) (C D : Constraint) : Prop :=
  Entails S M C D ∧ Entails S M D C

def Satisfiable (S : Signature) (M : Model) (C : Constraint) : Prop :=
  C.WF S [] 0 ∧ ∃ ρ ι, ρ.Valid S M ∧ ι.Valid M ∧ C.Holds S M ρ ι

def ArrowLaw (S : Signature) (M : Model) : Prop :=
  ∀ T U V W, T.HasKind S [] 0 → U.HasKind S [] 0 → V.HasKind S [] 0 → W.HasKind S [] 0 →
    Equivalent S M (.le 0 (.arrow T U) (.arrow V W)) (.conj (.le 0 V T) (.le 0 U W))

/-- Isolation is unchanged; it concerns the model, not the binding representation. -/
def Framework (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  M.Requirements S ∧ ArrowLaw S M ∧ HMX.Isolation S M I

def Scheme.IncludedUnder (S : Signature) (M : Model) (C : Constraint) (s r : Scheme) : Prop :=
  ∀ ρ ι, ρ.Valid S M → ι.Valid M → C.Holds S M ρ ι → s.denote S M ρ ι ⊆ r.denote S M ρ ι

end HMX.LN
