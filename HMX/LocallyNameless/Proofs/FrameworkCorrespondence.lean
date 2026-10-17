import HMX.LocallyNameless.Proofs.Encoding

namespace HMX.LN.Proofs

/-- The bound case is irrelevant at the empty stack; the kind proof excludes it. -/
def namedTy : Ty → HMX.Ty
  | .free X => .var X
  | .bound _ => .var (0, 0)
  | .con f ts => .con f (ts.map namedTy)

theorem namedTyKind (h : Ty.HasKind S [] T k) : (namedTy T).HasKind S k := by
  cases h with
  | free hk => simpa only [namedTy] using HMX.Ty.HasKind.var _ hk
  | bound hi _ => simp at hi
  | con hf ht =>
    simp only [namedTy]
    apply HMX.Ty.HasKind.con _ _ hf
    apply List.forall₂_map_left_iff.mpr
    exact forall₂ImplMem ht (fun U _ p hp => namedTyKind hp)
termination_by sizeOf T

theorem namedTyEncoding (T : Ty) (h : T.LCAt 0) : ofTy [] (namedTy T) = T := by
  cases T with
  | free X => simp [namedTy, ofTy]
  | bound i => simp [Ty.LCAt] at h
  | con f ts =>
    simp only [Ty.LCAt] at h
    simp only [namedTy, ofTy, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U hu => namedTyEncoding U (h U hu)) |>.trans (List.map_id ts)
termination_by sizeOf T

/-- Every well-kinded type at the empty stack has a named representative. -/
theorem namedTypeRepresentative (h : Ty.HasKind S [] T k) :
    ∃ U : HMX.Ty, U.HasKind S k ∧ ofTy [] U = T :=
  ⟨namedTy T, namedTyKind h, namedTyEncoding T (tyKindLC T S [] k h)⟩

theorem encodingClosedTyEval (T : HMX.Ty) (M : Model) (ρ : Assignment M) :
    (ofTy [] T).eval M ρ = T.eval M ρ :=
  encodingTyEval T [] M ρ ρ _ (fun _ => rfl)

theorem encodingSubtypeHolds (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) (k : Nat) (T U : HMX.Ty) :
    (Constraint.le k (ofTy [] T) (ofTy [] U)).Holds S M ρ ι ↔
      (HMX.Constraint.le k T U).Holds S M ρ ι := by
  change Predicate.eval M (.sub k) [(ofTy [] T).eval M ρ, (ofTy [] U).eval M ρ] ↔ _
  rw [encodingClosedTyEval, encodingClosedTyEval]
  rfl

theorem encodingArrowEquivalent (S : Signature) (M : Model)
    (T U V W : HMX.Ty) :
    Equivalent S M (.le 0 (.arrow (ofTy [] T) (ofTy [] U))
      (.arrow (ofTy [] V) (ofTy [] W)))
      (.conj (.le 0 (ofTy [] V) (ofTy [] T)) (.le 0 (ofTy [] U) (ofTy [] W))) ↔
    HMX.Equivalent S M (.le 0 (.arrow T U) (.arrow V W))
      (.conj (.le 0 V T) (.le 0 U W)) := by
  have ha : ofTy [] (.arrow T U) = .arrow (ofTy [] T) (ofTy [] U) := by simp [ofTy, HMX.Ty.arrow, Ty.arrow]
  have hb : ofTy [] (.arrow V W) = .arrow (ofTy [] V) (ofTy [] W) := by simp [ofTy, HMX.Ty.arrow, Ty.arrow]
  rw [← ha, ← hb]
  simp only [Equivalent, Entails, HMX.Equivalent, HMX.Entails,
    show ∀ C D ρ ι, (Constraint.conj C D).Holds S M ρ ι ↔
      C.Holds S M ρ ι ∧ D.Holds S M ρ ι from fun _ _ _ _ => Iff.rfl,
    HMX.Constraint.Holds, encodingSubtypeHolds]

theorem frameworkCorrespondence (S : Signature) (M : Model) (I : Set Nat) :
    HMX.LN.frameworkCorrespondence S M I := by
  constructor
  · rintro ⟨hm, ha, hi⟩
    refine ⟨hm, ?_, hi⟩
    intro T U V W hT hU hV hW
    exact (encodingArrowEquivalent S M T U V W).mp
      (ha _ _ _ _ (encodingTyKind hT []) (encodingTyKind hU [])
        (encodingTyKind hV []) (encodingTyKind hW []))
  · rintro ⟨hm, ha, hi⟩
    refine ⟨hm, ?_, hi⟩
    intro T U V W hT hU hV hW
    obtain ⟨T', ht, rfl⟩ := namedTypeRepresentative hT
    obtain ⟨U', hu, rfl⟩ := namedTypeRepresentative hU
    obtain ⟨V', hv, rfl⟩ := namedTypeRepresentative hV
    obtain ⟨W', hw, rfl⟩ := namedTypeRepresentative hW
    exact (encodingArrowEquivalent S M T' U' V' W').mpr (ha _ _ _ _ ht hu hv hw)

end HMX.LN.Proofs
