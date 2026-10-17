import HMX.LocallyNameless.Proofs.NamedSchemeConversion
import HMX.LocallyNameless.Proofs.TypingEquivalence
import HMX.LocallyNameless.Proofs.GenerationSemantics

namespace HMX.LN.Proofs

/- Count only constraint/scheme nodes, so opening leaves the induction measure unchanged. -/
mutual
def constraintNodes : Constraint → Nat
  | .truth | .falsity | .atom _ _ | .inst _ _ => 1
  | .conj C D => 1 + constraintNodes C + constraintNodes D
  | .exists_ _ C => 1 + constraintNodes C
  | .def_ _ s C => 1 + schemeNodes s + constraintNodes C
def schemeNodes : Scheme → Nat
  | .all _ C _ => 1 + constraintNodes C
end

theorem constraintNodesMapTypes (C : Constraint) (f : Nat → Ty → Ty) (d : Nat) :
    constraintNodes (C.mapTypes f d) = constraintNodes C := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, constraintNodes (C.mapTypes f d) = constraintNodes C)
    (motive_2 := fun s => ∀ d, schemeNodes (s.mapTypes f d) = schemeNodes s)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro C D ih ij d; simp only [Constraint.mapTypes,constraintNodes,ih,ij])
    (by intro ks C ih d; simp only [Constraint.mapTypes,constraintNodes,ih])
    (by intro b s C ih ij d; simp only [Constraint.mapTypes,constraintNodes,ih,ij])
    (by intros; rfl)
    (by intro ks C T ih d; simp only [Scheme.mapTypes,schemeNodes,ih]) C d

theorem constraintNodesMapIds (C : Constraint) (f : Nat → PVar → PVar) (d : Nat) :
    constraintNodes (C.mapIds f d) = constraintNodes C := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, constraintNodes (C.mapIds f d) = constraintNodes C)
    (motive_2 := fun s => ∀ d, schemeNodes (s.mapIds f d) = schemeNodes s)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro C D ih ij d; simp only [Constraint.mapIds,constraintNodes,ih,ij])
    (by intro ks C ih d; simp only [Constraint.mapIds,constraintNodes,ih])
    (by intro b s C ih ij d; simp only [Constraint.mapIds,constraintNodes,ih,ij])
    (by intros; rfl)
    (by intro ks C T ih d; simp only [Scheme.mapIds,schemeNodes,ih]) C d

theorem namedTyFv (T : Ty) (h : T.LCAt 0) : (namedTy T).fv = T.fv := by
  have he := encodingTyFv (namedTy T) []
  rw [namedTyEncoding T h] at he
  simpa using he.symm

theorem namedTyEval (T : Ty) (h : T.LCAt 0) (ρ : Assignment M) :
    (namedTy T).eval M ρ = T.eval M ρ := by
  rw [← encodingClosedTyEval, namedTyEncoding T h]

theorem assignmentBlockWitness (xs : List TVar) (ρ σ : Assignment M)
    (ha : ρ.AgreeOutside σ xs.toFinset) : assignBlock xs (xs.map σ) ρ = σ := by
  funext X
  by_cases hx : X ∈ xs
  · simp [assignBlock,hx,List.getElem?_map,List.getElem?_idxOf hx]
  · simpa [assignBlock,hx] using ha X (by simpa using hx)

theorem namedExistsList (xs : List TVar) (hk : ∀ X ∈ xs, X.1 ∈ S.kinds)
    (D : HMX.Constraint) (ρ : Assignment M) (ι : GroundEnv M) (hρ : ρ.Valid S M) :
    (HMX.Constraint.exists_ xs.toFinset D).Holds S M ρ ι ↔
      ∃ vs, List.Forall₂ (fun v X => M.kind v = X.1) vs xs ∧
        D.Holds S M (assignBlock xs vs ρ) ι := by
  constructor
  · rintro ⟨σ,hσ,ha,hD⟩
    exact ⟨xs.map σ,assignmentBlockKinds S M σ xs hσ hk,by rw [assignmentBlockWitness xs ρ σ ha]; exact hD⟩
  · rintro ⟨vs,hvs,hD⟩
    refine ⟨assignBlock xs vs ρ,assignBlockValid S M ρ xs vs hρ hvs,?_,hD⟩
    intro X hx; simp only [List.mem_toFinset] at hx
    simp [assignBlock,hx]

theorem namedGeneralizeList (xs : List TVar) (hk : ∀ X ∈ xs, X.1 ∈ S.kinds)
    (D : HMX.Constraint) (T : HMX.Ty) (ρ : Assignment M) (ι : GroundEnv M) (hρ : ρ.Valid S M)
    (v : M.Carrier) :
    v ∈ (HMX.Scheme.all xs.toFinset D T).denote S M ρ ι ↔
      M.kind v = 0 ∧ ∃ vs, List.Forall₂ (fun v X => M.kind v = X.1) vs xs ∧
        D.Holds S M (assignBlock xs vs ρ) ι ∧ M.below 0 (T.eval M (assignBlock xs vs ρ)) v := by
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨σ,hσ,ha,hD,hT⟩
    exact ⟨xs.map σ,assignmentBlockKinds S M σ xs hσ hk,by rw [assignmentBlockWitness xs ρ σ ha]; exact ⟨hD,hT⟩⟩
  · rintro ⟨vs,hvs,hD,hT⟩
    refine ⟨assignBlock xs vs ρ,assignBlockValid S M ρ xs vs hρ hvs,?_,hD,hT⟩
    intro X hx; simp only [List.mem_toFinset] at hx
    simp [assignBlock,hx]

theorem freshExistsOpening (ks : List Nat) (C : Constraint)
    (hw : (Constraint.exists_ ks C).WF S [] 0) :
    ∃ xs D, xs.Nodup ∧ (∀ X ∈ xs, X.1 ∈ S.kinds) ∧ D.WF S [] 0 ∧
      D.existsNames xs = .exists_ ks C ∧ constraintNodes D = constraintNodes C := by
  obtain ⟨xs,hks,hn,hf⟩ := freshKinds ks C.fv
  let D := C.openTypes (xs.map Ty.free)
  have hx : ∀ X ∈ xs, X.1 ∈ S.kinds := fun X hx => hw.1 X.1 (hks ▸ List.mem_map.mpr ⟨X,hx,rfl⟩)
  have hu : List.Forall₂ (Ty.HasKind S []) (xs.map Ty.free) ks := by
    rw [← hks]
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun X hx' => .free (hx X hx'))
  refine ⟨xs,D,hn,hx,typeOpeningWF S ks _ C (by simpa using hw.2) hu,?_,constraintNodesMapTypes C _ 0⟩
  simp only [Constraint.existsNames,D,Constraint.closeTypes,Constraint.openTypes,hks]
  rw [constraintCloseOpen xs C 0 hn hf]

end HMX.LN.Proofs
