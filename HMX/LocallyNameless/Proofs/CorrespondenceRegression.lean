import HMX.LocallyNameless.Proofs.InferenceTransfer

namespace HMX.LN.Proofs

def shadowedConstantConstraint : Constraint :=
  .def_ (.constant 0) (.mono (.free (0,0)))
    (.def_ (.constant 0) (.mono (.free (0,0))) (.inst (.bound 1) (.free (0,0))))

theorem shadowedConstantWF (h0 : 0 ∈ S.kinds) : shadowedConstantConstraint.WF S [] 0 :=
  ⟨monoWFAt S _ 0 (.free h0),monoWFAt S _ 1 (.free h0),.free h0,by decide⟩

theorem encodingConstantDefBody (xs : List TVar) (zs : List Id) (c : Nat)
    (s : Scheme) (D : Constraint) (C : HMX.Constraint)
    (h : ofConstraint xs zs C = .def_ (.constant c) s D) :
    ∃ E : HMX.Constraint, ofConstraint xs (.const c :: zs) E = D := by
  cases C with
  | def_ x sn E =>
    simp only [ofConstraint,Constraint.def_.injEq] at h
    cases x with
    | var n => cases h.1
    | loc n => cases h.1
    | const n =>
      have hn := Binder.constant.inj h.1
      subst n
      exact ⟨E,h.2.2⟩
  | truth | falsity | atom _ _ | conj _ _ | exists_ _ _ | inst _ _ =>
    simp only [ofConstraint] at h
    cases h

/-- A representation counterexample, not a counterexample to typing correspondence. -/
theorem shadowedConstantNotEncoding :
    ¬ ∃ C : HMX.Constraint, ofConstraint [] [] C = shadowedConstantConstraint := by
  rintro ⟨C,h⟩
  obtain ⟨D,hD⟩ := encodingConstantDefBody [] [] 0 _ _ C h
  obtain ⟨E,hE⟩ := encodingConstantDefBody [] [.const 0] 0 _ _ D hD
  cases E with
  | inst x T =>
    have hx := (Constraint.inst.inj hE).1
    cases x with
    | var n => simp [ofId] at hx
    | loc n => simp [ofId] at hx
    | const n =>
      by_cases hn : n = 0
      · subst n; simp [ofId] at hx
      · simp [ofId,hn] at hx
  | truth | falsity | atom _ _ | conj _ _ | exists_ _ _ | def_ _ _ _ =>
    simp only [ofConstraint] at hE
    cases hE

theorem shadowedConstantSemantics (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M) :
    shadowedConstantConstraint.Holds S M ρ ι ↔
      (Constraint.def_ .term (.mono (.free (0,0)))
        (.def_ .term (.mono (.free (0,0))) (.inst (.bound 1) (.free (0,0))))).Holds S M ρ ι := Iff.rfl

def unusedImpossibleEnv : HMX.Env :=
  [(.const 0,.mono (.var (0,0))),(.const 1,.all ∅ .falsity (.var (0,0)))]

theorem unusedImpossibleEnvTyping (h0 : 0 ∈ S.kinds) :
    HMX.Typing S M .truth unusedImpossibleEnv (.ident (.const 0)) (.mono (.var (0,0))) := by
  have hT : (HMX.Ty.var (0,0)).HasKind S 0 := .var _ h0
  have hs : (HMX.Scheme.mono (.var (0,0))).WF S := ⟨by simp,trivial,hT⟩
  have hr : (HMX.Scheme.all ∅ .falsity (.var (0,0))).WF S := ⟨by simp,trivial,hT⟩
  refine ⟨_,.var ⟨trivial,?_,hs,rfl,rfl,rfl⟩ (by simp [unusedImpossibleEnv,lookup]) ?_⟩
  · intro p hp
    simp only [unusedImpossibleEnv,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> assumption
  · intro ρ ι hρ _ _
    exact ⟨ρ,hρ,fun _ _ => rfl,trivial⟩

theorem unusedImpossibleEnvNotRealizable (S : Signature) (M : Model)
    (ρ : Assignment M) (ι : GroundEnv M) : ¬ unusedImpossibleEnv.exists_.Holds S M ρ ι := by
  simp [unusedImpossibleEnv,HMX.Env.exists_,HMX.Env.defIn,HMX.Scheme.exists_,HMX.Scheme.mono,
    HMX.Constraint.Holds]

theorem unusedImpossibleEnvLNTyping (hM : M.Requirements S) :
    Typing S M .truth (ofEnv unusedImpossibleEnv) (.ident (.free (.const 0))) (.mono (.free (0,0))) := by
  have hp := encodingTyping hM (unusedImpossibleEnvTyping (M := M) hM.1.1)
  simpa only [encodingMono,ofTy,ofExpr,ofId,ofConstraint,List.not_mem_nil,↓reduceIte] using hp

/-- Named soundness does not require the whole environment to be realizable. -/
theorem unusedImpossibleEnvInferenceSoundness (hF : HMX.Framework S M I) :
    HMX.Typing S M (HMX.infer unusedImpossibleEnv (.ident (.const 0)) (.var (0,0)))
      unusedImpossibleEnv (.ident (.const 0)) (.mono (.var (0,0))) := by
  have hw := HMX.Proofs.derivationWF (unusedImpossibleEnvTyping (M := M) hF.1.1.1).choose_spec
  exact HMX.Proofs.theorem10_4_4_soundness_scoped S M I hF _ _ _ hw.2.1 hw.2.2.2.2.1
    (by simp [HMX.Expr.fpi,HMX.Env.dpi,unusedImpossibleEnv]) (.var _ hF.1.1.1)

end HMX.LN.Proofs
