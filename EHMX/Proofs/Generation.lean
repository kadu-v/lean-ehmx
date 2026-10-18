import EHMX.Inference
import EHMX.Proofs.TypeSubstitution

namespace EHMX

private theorem leWF (hk : k ∈ S.kinds) (hT : Ty.HasKind S Δ T k)
    (hU : Ty.HasKind S Δ U k) : (Constraint.le k T U).WF S Δ n :=
  ⟨hk, .cons hT (.cons hU .nil)⟩

private theorem resultWF (hS : S.WF) (hA : Ty.HasKind S Δ A 0)
    (hT : Ty.HasKind S Δ T 0) (hη : Ty.HasKind S Δ η 1) (hε : Ty.HasKind S Δ ε 1) :
    (resultConstraint A T η ε).WF S Δ n :=
  ⟨leWF hS.1 hA hT, leWF hS.2.1 hη hε⟩

private theorem monoWF (hT : Ty.HasKind S Δ T 0) : (Scheme.mono T).WF S Δ n :=
  ⟨by simp, trivial, hT⟩

/-- Generation is well-kinded even for rejected undeclared operations (falsity).
No inference soundness or satisfiability assumption is used. -/
theorem generationWF (hS : S.WF) (hsig : OpSignature.WF S sig)
    (he : e.LCAt n) (hT : Ty.HasKind S Δ T 0) (hε : Ty.HasKind S Δ ε 1) :
    (generate sig e T ε).WF S Δ n := by
  induction e generalizing Δ n T ε with
  | ident x =>
      refine ⟨⟨hT, ?_⟩, leWF hS.2.1 (emptyKind hS) hε⟩
      cases x <;> exact he
  | lam body ih =>
      simp only [generate, Constraint.WF]
      refine ⟨by simp [hS.1, hS.2.1], ?_⟩
      have ha : Ty.HasKind S ([0,1,0] ++ Δ) (.bound 0) 0 := .bound rfl hS.1
      have hη : Ty.HasKind S ([0,1,0] ++ Δ) (.bound 1) 1 := .bound rfl hS.2.1
      have hb : Ty.HasKind S ([0,1,0] ++ Δ) (.bound 2) 0 := .bound rfl hS.1
      exact ⟨⟨monoWF ha, ih he hb hη⟩,
        resultWF hS (arrowKind ha hη hb) (kindShift hT _) (emptyKind hS) (kindShift hε _)⟩
  | app f x ihf ihx =>
      simp only [generate, Constraint.WF]
      refine ⟨by simp [hS.1, hS.2.1], ?_⟩
      have ha : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 0) 0 := .bound rfl hS.1
      have hη : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 1) 1 := .bound rfl hS.2.1
      have hef : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 2) 1 := .bound rfl hS.2.1
      have hex : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 3) 1 := .bound rfl hS.2.1
      exact ⟨ihf he.1 (arrowKind ha hη (kindShift hT _)) hef,
        ihx he.2 ha hex, leWF hS.2.1 (unionKind (unionKind hη hef) hex) (kindShift hε _)⟩
  | letE rhs body ihr ihb =>
      simp only [generate]
      split
      · simp only [Constraint.letBound, Constraint.WF, Scheme.exists_, Scheme.WF]
        have ha : Ty.HasKind S ([0] ++ Δ) (.bound 0) 0 := .bound rfl hS.1
        have hr := ihr (Δ := [0] ++ Δ) he.1 ha (emptyKind hS)
        exact ⟨⟨by simp [hS.1], hr⟩,
          ⟨by simp [hS.1], hr, ha⟩, ihb he.2 hT hε⟩
      · simp only [Constraint.WF]
        refine ⟨by simp [hS.1, hS.2.1], ?_⟩
        have ha : Ty.HasKind S ([0,1,1] ++ Δ) (.bound 0) 0 := .bound rfl hS.1
        have her : Ty.HasKind S ([0,1,1] ++ Δ) (.bound 1) 1 := .bound rfl hS.2.1
        have heb : Ty.HasKind S ([0,1,1] ++ Δ) (.bound 2) 1 := .bound rfl hS.2.1
        exact ⟨ihr he.1 ha her, ⟨monoWF ha, ihb he.2 (kindShift hT _) heb⟩,
          leWF hS.2.1 (unionKind her heb) (kindShift hε _)⟩
  | perform op arg ih =>
      simp only [generate]
      split
      · trivial
      · rename_i decl hd
        have hdecl := hsig op decl hd
        have hη : Ty.HasKind S ((decl.kinds ++ [1]) ++ Δ) (.bound decl.kinds.length) 1 :=
          .bound (by simp) hS.2.1
        have ha := kindAppend hdecl.2.1 ([1] ++ Δ)
        have hb := kindAppend hdecl.2.2.1 ([1] ++ Δ)
        simp only [Constraint.WF, List.append_assoc] at hη ⊢
        refine ⟨?_, termDepthWF.1 _ _ 0 n (constraintAppendWF hdecl.2.2.2.2.2.1 _) (Nat.zero_le _), ih he ha hη, resultWF hS hb ?_ (unionKind (singletonKind op) hη) ?_⟩
        · simp only [List.mem_append, List.mem_singleton]
          intro k hk; rcases hk with hk | rfl
          exact hdecl.1 k hk
          exact hS.2.1
        · have H := kindShift hT (decl.kinds ++ [1])
          rw [List.length_append, List.length_cons, List.length_nil, List.append_assoc] at H
          exact H
        · have H := kindShift hε (decl.kinds ++ [1])
          rw [List.length_append, List.length_cons, List.length_nil, List.append_assoc] at H
          exact H
  | handle body op ret clause ihb ihr ihc =>
      simp only [generate]
      split
      · trivial
      · rename_i decl hd
        have hdecl := hsig op decl hd
        let Δ' := [0,1,0,1] ++ Δ
        have ha : Ty.HasKind S Δ' (.bound 0) 0 := .bound rfl hS.1
        have hei : Ty.HasKind S Δ' (.bound 1) 1 := .bound rfl hS.2.1
        have hb : Ty.HasKind S Δ' (.bound 2) 0 := .bound rfl hS.1
        have heo : Ty.HasKind S Δ' (.bound 3) 1 := .bound rfl hS.2.1
        have hopa := kindAppend hdecl.2.1 Δ'
        have hopb := kindAppend hdecl.2.2.1 Δ'
        exact ⟨by simp [hS.1, hS.2.1], ihb he.1 ha hei,
          leWF hS.2.1 hei (unionKind (singletonKind op) heo),
          ⟨monoWF ha, ihr he.2.1 hb heo⟩,
          ⟨hdecl.1, constraintAppendWF hdecl.2.2.2.2.2.1 _, hdecl.2.2.2.2.2.2.1, monoWF hopa,
            monoWF (arrowKind hopb (kindShift heo _) (kindShift hb _)),
            ihc he.2.2 (kindShift hb _) (kindShift heo _)⟩,
          resultWF hS hb (kindShift hT _) heo (kindShift hε _)⟩

theorem generationScope (hsig : OpSignature.WF S sig) (hd : e.Declared sig) :
    (generate sig e T ε).fpi = e.fv := by
  induction e generalizing T ε with
  | ident x => cases x <;> simp [generate, Constraint.fpi, Expr.fv, Constraint.le]
  | lam body ih =>
      simp [generate, resultConstraint, Constraint.le, Constraint.fpi, Scheme.fpi,
        Scheme.mono, ih hd, Expr.fv]
  | app f x ihf ihx =>
      simp [generate, Constraint.le, Constraint.fpi, ihf hd.1, ihx hd.2, Expr.fv]
  | letE rhs body ihr ihb =>
      simp only [generate]
      split <;> simp [Constraint.letBound, Scheme.exists_, Scheme.mono, Constraint.le,
        Constraint.fpi, Scheme.fpi, ihr hd.1, ihb hd.2, Expr.fv]
  | perform op arg ih =>
      cases hs : sig op with
      | none => exact False.elim (hd.1 hs)
      | some decl =>
          simp [generate, hs, (hsig op decl hs).2.2.2.2.2.2.1, resultConstraint, Constraint.le, Constraint.fpi,
            ih hd.2, Expr.fv]
  | handle body op ret clause ihb ihr ihc =>
      cases hs : sig op with
      | none => exact False.elim (hd.1 hs)
      | some decl =>
          simp [generate, hs, (hsig op decl hs).2.2.2.2.2.2.1, resultConstraint, Constraint.le, Constraint.fpi,
            Scheme.fpi, Scheme.mono, ihb hd.2.1, ihr hd.2.2.1, ihc hd.2.2.2,
            Expr.fv, Finset.union_assoc]

end EHMX
