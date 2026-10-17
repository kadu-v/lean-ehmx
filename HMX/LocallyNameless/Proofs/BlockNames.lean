import HMX.LocallyNameless.Proofs.PermutationWF

namespace HMX.LN.Proofs

theorem permuteBlockNames (hp : BlockPermutation ks ls p) (xs : List TVar)
    (hx : xs.Nodup) (hxs : xs.map Prod.fst = ks) :
    ∃ ys : List TVar, ys.Nodup ∧ ys.map Prod.fst = ls ∧ ys.toFinset = xs.toFinset ∧
      ∀ i, ys[p i]? = xs[i]? := by
  classical
  let e := Equiv.ofBijective p hp.2.1
  have hlen : xs.length = ks.length := by simpa using congrArg List.length hxs
  have hb : ∀ j : Fin ls.length, e.symm j < xs.length := by
    intro j
    rw [hlen]
    apply (blockPermutationBound ks ls e hp _).mpr
    simpa only [Equiv.apply_symm_apply] using j.isLt
  let ys := List.ofFn (fun j : Fin ls.length => xs.get ⟨e.symm j,hb j⟩)
  have hylen : ys.length = ls.length := List.length_ofFn
  have hi : ∀ i, ys[p i]? = xs[i]? := by
    intro i
    by_cases h : i < ks.length
    · have hpi := (blockPermutationBound ks ls p hp i).mp h
      have hxi : i < xs.length := by omega
      simp only [ys,List.getElem?_ofFn,hpi,↓reduceDIte,List.get_eq_getElem]
      change some (xs.get ⟨e.symm (e i),by simpa using hxi⟩) = xs[i]?
      simp [List.getElem?_eq_getElem hxi]
    · have hpi : ¬ p i < ls.length := fun hh => h ((blockPermutationBound ks ls p hp i).mpr hh)
      simp [ys,hpi,List.getElem?_eq_none (show xs.length ≤ i by omega)]
  have hyn : ys.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j hij
    have heq := hx.injective_get hij
    apply Fin.ext
    apply e.symm.injective
    exact congrArg Fin.val heq
  have hyks : ys.map Prod.fst = ls := by
    apply List.ext_getElem?
    intro i
    obtain ⟨j,rfl⟩ := hp.2.1.2 i
    rw [List.getElem?_map,hi,← List.getElem?_map,hxs,hp.2.2.2 j]
  have hset : ys.toFinset = xs.toFinset := by
    ext X
    simp only [List.mem_toFinset]
    constructor
    · intro h
      obtain ⟨i,hi',hget⟩ := List.mem_iff_getElem.mp h
      obtain ⟨j,rfl⟩ := hp.2.1.2 i
      exact List.mem_of_getElem? ((hi j).symm.trans (List.getElem?_eq_some_iff.mpr ⟨hi',hget⟩))
    · intro h
      obtain ⟨i,hi',hget⟩ := List.mem_iff_getElem.mp h
      exact List.mem_of_getElem? ((hi i).trans (List.getElem?_eq_some_iff.mpr ⟨hi',hget⟩))
  exact ⟨ys,hyn,hyks,hset,hi⟩

theorem tyOpenPermutedBlock (T : Ty) (hp : BlockPermutation ks ls p) (xs ys : List TVar)
    (hlen : xs.length = ks.length) (hylen : ys.length = ls.length)
    (hi : ∀ i, ys[p i]? = xs[i]?) (d : Nat) :
    (T.renameAt d p).openAt d (ys.map Ty.free) = T.openAt d (xs.map Ty.free) := by
  induction T using tyInduction with
  | hf X => simp [Ty.renameAt,Ty.openAt]
  | hb i =>
    by_cases h : i < d
    · simp [Ty.renameAt,Ty.openAt,h]
    · simp only [Ty.renameAt,h,↓reduceIte,Ty.openAt,
        show ¬ d + p (i-d) < d by omega,↓reduceIte,Nat.add_sub_cancel_left,
        List.getElem?_map,hi]
      cases hg : xs[i-d]? with
      | some X => rfl
      | none =>
        have hp' := hp.2.2.1 (i-d) (by have h' := List.getElem?_eq_none_iff.mp hg; omega)
        simp only [Option.map_none,List.length_map,hp',hlen,hylen,← hp.1]
        congr 1; omega
  | hc f ts ih =>
    simp only [Ty.renameAt,Ty.openAt,List.map_map,Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U hu => ih U hu)

theorem constraintOpenPermutedBlock (C : Constraint) (hp : BlockPermutation ks ls p) (xs ys : List TVar)
    (hlen : xs.length = ks.length) (hylen : ys.length = ls.length)
    (hi : ∀ i, ys[p i]? = xs[i]?) (d : Nat) :
    (C.mapTypes (fun i T => T.renameAt i p) d).mapTypes (fun i T => T.openAt i (ys.map Ty.free)) d =
      C.mapTypes (fun i T => T.openAt i (xs.map Ty.free)) d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d,
      (C.mapTypes (fun i T => T.renameAt i p) d).mapTypes (fun i T => T.openAt i (ys.map Ty.free)) d =
        C.mapTypes (fun i T => T.openAt i (xs.map Ty.free)) d)
    (motive_2 := fun s => ∀ d,
      (s.mapTypes (fun i T => T.renameAt i p) d).mapTypes (fun i T => T.openAt i (ys.map Ty.free)) d =
        s.mapTypes (fun i T => T.openAt i (xs.map Ty.free)) d)
    (by intros; rfl) (by intros; rfl)
    (by intro q ts d; simp only [Constraint.mapTypes,List.map_map,Function.comp_def]; congr 1;
        exact List.map_congr_left (fun T _ => tyOpenPermutedBlock T hp xs ys hlen hylen hi d))
    (by intro C D ih ij d; exact congrArg₂ Constraint.conj (ih d) (ij d))
    (by intro bs C ih d; exact congrArg (Constraint.exists_ bs) (ih _))
    (by intro b s C ih ij d; exact congrArg₂ (Constraint.def_ b) (ih d) (ij d))
    (by intro x T d; exact congrArg (Constraint.inst x) (tyOpenPermutedBlock T hp xs ys hlen hylen hi d))
    (by
      intro bs C T ih d
      exact congrArg₂ (Scheme.all bs) (ih _)
        (tyOpenPermutedBlock T hp xs ys hlen hylen hi _)) C d

end HMX.LN.Proofs
