import EHMX.HMX.GenerationCompleteness

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}
open Inference

/-- Every returned constraint has a derivation, independently of satisfiability. -/
theorem generate_sound (sig : Signature T) (X : Constraints T O) (N : X.Simplifier)
    (hsig : sig.Closed) (e : Expr) :
    ∀ (g : Context X) (t : T.Term) (eff : Effect) (fixed : Names),
      (Inference.Protected X g t eff).Subset fixed →
      ∀ d, generate sig X N e g t eff fixed = some d →
      Inference sig X N X.top g e t eff d := by
  induction e with
  | var i =>
    intro g t eff fixed hf d run
    simp only [generate, Option.map_eq_some_iff] at run
    obtain ⟨s, found, rfl⟩ := run
    cases s with
    | mono a => exact .varMono found
    | qualified bound c a => exact .varPoly _ found (fun _ h => h) (fun _ h => h)
  | int n =>
    intro g t eff fixed hf d run
    cases Option.some.inj run
    exact .int n
  | bool b =>
    intro g t eff fixed hf d run
    cases Option.some.inj run
    exact .bool b
  | lam body ih =>
    intro g t eff fixed hfixed output run
    let p := fixed.shiftTypes 0
    let q := fixed.shiftTypes 1
    let m := fixed.shiftEffects 0
    let a := T.var p
    let b := T.var q
    let latent := Effect.var m
    let childContext : Context X := .mono a :: g
    let locals : Names := ⟨{p, q}, {m}⟩
    let childFixed := fixed.union ((Inference.Protected X childContext b latent).union locals)
    have hchild : (Inference.Protected X childContext b latent).Subset childFixed :=
      (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
    have houter : fixed.Subset childFixed := Names.subset_union_left _ _
    have hlocal : locals.Subset childFixed :=
      (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
    have hgfixed : g.support.Subset fixed := (Protected.context g t eff).trans hfixed
    have htFixed : (T.support t).Subset fixed := (Protected.type g t eff).trans hfixed
    change (generate sig X N body childContext b latent childFixed >>= _) = some output at run
    obtain ⟨d, hd, heq⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj heq
    exact .lam (ih childContext b latent childFixed hchild d hd)
  | app f x ihf ihx =>
    intro g t eff fixed hfixed output run
    let ft := T.var (fixed.shiftTypes 0)
    let xt := T.var (fixed.shiftTypes 1)
    let ef := Effect.var (fixed.shiftEffects 0)
    let ex := Effect.var (fixed.shiftEffects 1)
    let latent := Effect.var (fixed.shiftEffects 2)
    let bothFixed := fixed.union ((Protected X g ft ef).union
      ((Protected X g xt ex).union ⟨∅, latent.vars⟩))
    have hfun : (Protected X g ft ef).Subset bothFixed :=
      (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
    have harg : (Protected X g xt ex).Subset bothFixed :=
      (Names.subset_union_left _ _).trans
        ((Names.subset_union_right _ _).trans (Names.subset_union_right _ _))
    have houter : fixed.Subset bothFixed := Names.subset_union_left _ _
    have hlat : latent.vars ⊆ bothFixed.effects :=
      Finset.subset_union_right.trans (Finset.subset_union_right.trans Finset.subset_union_right)
    change (generate sig X N f g ft ef bothFixed >>= _) = some output at run
    obtain ⟨df, runf, run⟩ := Option.bind_eq_some_iff.mp run
    change (generate sig X N x g xt ex (bothFixed.union (X.support df)) >>= _) = some output at run
    obtain ⟨dx, runx, heq⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj heq
    exact .app (ihf g ft ef bothFixed hfun df runf)
      (ihx g xt ex _ (harg.trans (Names.subset_union_left _ _)) dx runx)
  | letE val body ihv ihb =>
    intro g t eff fixed hfixed output run
    by_cases hv : Value val
    · rw [generate, ite_eq_left ((Value.isValue_iff val).mpr hv)] at run
      let a := T.var (fixed.shiftTypes 0)
      let valFixed := fixed.union (Protected X g a ∅)
      have hval : (Protected X g a ∅).Subset valFixed := Names.subset_union_right _ _
      have houter : fixed.Subset valFixed := Names.subset_union_left _ _
      have hgfixed := (Protected.context g t eff).trans hfixed
      change (generate sig X N val g a ∅ valFixed >>= _) = some output at run
      obtain ⟨dv, runv, run⟩ := Option.bind_eq_some_iff.mp run
      let scheme := Scheme.generalize g (N.run dv) a
      let projected := X.existsNames (g.generalizationNames (N.run dv) a) (N.run dv)
      let newContext : Context X := scheme :: g
      let bodyFixed := fixed.union ((Inference.Protected X newContext t eff).union (X.support projected))
      have hbFixed : (Inference.Protected X newContext t eff).Subset bodyFixed :=
        (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
      change (generate sig X N body newContext t eff bodyFixed >>= _) = some output at run
      obtain ⟨db, runb, heq⟩ := Option.bind_eq_some_iff.mp run
      cases Option.some.inj heq
      exact .letVal hv (g.generalizationNames_avoids (N.run dv) a)
        (ihv g a ∅ valFixed hval dv runv) (ihb newContext t eff bodyFixed hbFixed db runb)
    · rw [generate, ite_eq_right (fun h => hv ((Value.isValue_iff val).mp h))] at run
      let a := T.var (fixed.shiftTypes 0)
      let ev := Effect.var (fixed.shiftEffects 0)
      let eb := Effect.var (fixed.shiftEffects 1)
      let bodyContext : Context X := .mono a :: g
      let bothFixed := fixed.union ((Protected X g a ev).union (Protected X bodyContext t eb))
      have hval : (Protected X g a ev).Subset bothFixed :=
        (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
      have hbody : (Protected X bodyContext t eb).Subset bothFixed :=
        (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
      have houter : fixed.Subset bothFixed := Names.subset_union_left _ _
      change (generate sig X N val g a ev bothFixed >>= _) = some output at run
      obtain ⟨dv, runv, run⟩ := Option.bind_eq_some_iff.mp run
      change (generate sig X N body bodyContext t eb (bothFixed.union (X.support dv)) >>= _) = some output at run
      obtain ⟨db, runb, heq⟩ := Option.bind_eq_some_iff.mp run
      cases Option.some.inj heq
      exact .letMono hv (ihv g a ev bothFixed hval dv runv)
        (ihb bodyContext t eb _ (hbody.trans (Names.subset_union_left _ _)) db runb)
  | perform op arg ih =>
    intro g t eff fixed hfixed output run
    change (sig op >>= _) = some output at run
    obtain ⟨raw, hs, run⟩ := Option.bind_eq_some_iff.mp run
    have hclosed := hsig op raw hs
    let sub := Substitution.freshen T raw.bound fixed.shiftTypes fixed.shiftEffects
    let tin := sub.apply raw.input
    let tout := sub.apply raw.output
    let keep := fixed.union ((T.support tin).union (T.support tout))
    let ea := Effect.var (keep.shiftEffects 0)
    let argFixed := keep.union (Protected X g tin ea)
    have hinput : (T.support tin).Subset keep :=
      (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
    have houtput : (T.support tout).Subset keep :=
      (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
    have hkeep : keep.Subset argFixed := Names.subset_union_left _ _
    have harg : (Protected X g tin ea).Subset argFixed := Names.subset_union_right _ _
    have houter : fixed.Subset keep := Names.subset_union_left _ _
    change (generate sig X N arg g tin ea argFixed >>= _) = some output at run
    obtain ⟨d, rund, heq⟩ := Option.bind_eq_some_iff.mp run
    cases Option.some.inj heq
    exact .perform sub hs hclosed (fun _ h => h) (fun _ h => h)
      (ih g tin ea argFixed harg d rund)
  | handle body op ret clause ihb ihr ihc =>
    intro g target out fixed hf output run
    change (sig op >>= _) = some output at run
    obtain ⟨raw, hs, run⟩ := Option.bind_eq_some_iff.mp run
    have hc := hsig op raw hs
    let input := T.var (fixed.shiftTypes 0)
    let result := T.var (fixed.shiftTypes 1)
    let ein := Effect.var (fixed.shiftEffects 0)
    let er := Effect.var (fixed.shiftEffects 1)
    let rest := Effect.var (fixed.shiftEffects 2)
    let core := fixed.union ((T.support input).union ((T.support result).union
      ⟨∅, ein.vars ∪ er.vars ∪ rest.vars⟩))
    have hfixed : fixed.Subset core := Names.subset_union_left _ _
    have hi : (T.support input).Subset core :=
      (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
    have hr : (T.support result).Subset core :=
      (Names.subset_union_left _ _).trans ((Names.subset_union_right _ _).trans (Names.subset_union_right _ _))
    have hgs : g.support.Subset core := ((Protected.context g target out).trans hf).trans hfixed
    have hts : (T.support target).Subset core := ((Protected.type g target out).trans hf).trans hfixed
    have hes : ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars ⊆ core.effects := by
      intro i hm
      simp only [Finset.mem_union] at hm
      rcases hm with ((hin | her) | hrest) | hout
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hin))))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_union_right _ her))))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_right _ hrest)))
      · exact hfixed.2 (hf.2 (Protected.effect g target out hout))
    have heval (v w : Valuation T.Value) (hw : w.AgreeOn v core) (eff : Effect)
        (he : eff.vars ⊆ core.effects) : eff.eval w.effects = eff.eval v.effects := by
      unfold Effect.eval
      congr 1
      exact Finset.biUnion_congr rfl (fun i hi => hw.2 i (he hi))
    have hein : ein.vars ⊆ core.effects :=
      (Finset.subset_union_left.trans Finset.subset_union_left).trans (Finset.subset_union_left.trans hes)
    have her : er.vars ⊆ core.effects :=
      (Finset.subset_union_right.trans Finset.subset_union_left).trans (Finset.subset_union_left.trans hes)
    have hrest : rest.vars ⊆ core.effects := Finset.subset_union_right.trans (Finset.subset_union_left.trans hes)
    have hout : out.vars ⊆ core.effects := Finset.subset_union_right.trans hes
    have hbprot : (Protected X g input ein).Subset core := by
      constructor <;> intro i hm
      · rcases Finset.mem_union.mp hm with hm | hm
        · rcases Finset.mem_union.mp hm with hm | hm
          · exact hgs.1 hm
          · exact hi.1 hm
        · exact False.elim (Finset.notMem_empty _ hm)
      · rcases Finset.mem_union.mp hm with hm | hm
        · rcases Finset.mem_union.mp hm with hm | hm
          · exact hgs.2 hm
          · exact hi.2 hm
        · exact hein hm
    change (generate sig X N body g input ein core >>= _) = some output at run
    obtain ⟨db, runb, run⟩ := Option.bind_eq_some_iff.mp run
    have hdb := ihb g input ein core hbprot db runb
    let rf := core.union (X.support db)
    have hcr : core.Subset rf := Names.subset_union_left _ _
    have hrprot : (Protected X (.mono input :: g) result er).Subset rf := by
      constructor <;> intro i hm
      · simp only [Protected, Context.support, List.foldr_cons, Scheme.support,
          Names.union, Finset.mem_union, Finset.notMem_empty, or_false] at hm
        rcases hm with (hm | hm) | hm
        · exact hcr.1 (hi.1 hm)
        · exact hcr.1 (hgs.1 hm)
        · exact hcr.1 (hr.1 hm)
      · simp only [Protected, Context.support, List.foldr_cons, Scheme.support,
          Names.union, Finset.mem_union] at hm
        rcases hm with ((hm | hm) | hm) | hm
        · exact hcr.2 (hi.2 hm)
        · exact hcr.2 (hgs.2 hm)
        · exact hcr.2 (hr.2 hm)
        · exact hcr.2 (her hm)
    change (generate sig X N ret (.mono input :: g) result er rf >>= _) = some output at run
    obtain ⟨dr, runr, run⟩ := Option.bind_eq_some_iff.mp run
    have hdr := ihr (.mono input :: g) result er rf hrprot dr runr
    let outer := rf.union (X.support dr)
    have hro : rf.Subset outer := Names.subset_union_left _ _
    have hco := hcr.trans hro
    let decl := raw.rename outer.shiftTypes outer.shiftEffects
    have fresh : raw.FreshInstance decl :=
      ⟨_, _, outer.shiftTypes_injective.injOn, outer.shiftEffects_injective.injOn, rfl⟩
    have hrigid : decl.bound.Disjoint outer :=
      ⟨outer.shiftTypes_disjoint raw.bound, outer.shiftEffects_disjoint raw.bound⟩
    let cg : Context X := .mono (T.arrow decl.output out result) :: .mono decl.input :: g
    let cf := outer.union ((Protected X cg result out).union
      (((T.support decl.input).union (T.support decl.output)).union decl.bound))
    have hoc : outer.Subset cf := Names.subset_union_left _ _
    have hcp : (Protected X cg result out).Subset cf :=
      (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
    let eo := Effect.var (cf.shiftEffects 0)
    let childFixed := cf.union (Inference.Protected X cg result eo)
    change (generate sig X N clause cg result eo childFixed >>= _) = some output at run
    obtain ⟨dc, runc, heq⟩ := Option.bind_eq_some_iff.mp run
    have hdc := ihc cg result eo childFixed (Names.subset_union_right _ _) dc runc
    let hidden := ((X.support dc).union ⟨∅, eo.vars⟩).diff cf
    have hhidden : hidden.Disjoint cf := by
      constructor <;> apply Finset.disjoint_left.mpr <;> intro i hi hf
      · exact (Finset.mem_sdiff.mp hi).2 hf
      · exact (Finset.mem_sdiff.mp hi).2 hf
    let cq := X.clause decl.bound hidden (X.and dc (X.and (X.le result result) (X.effectLe eo out)))
    let d := X.handler X.top db dr dc decl op result result result ein er eo rest out hidden
    have shape (v : Valuation T.Value) : X.holds d v ↔
        X.holds db v ∧ X.holds dr v ∧ X.holds cq v ∧
        rest.eval v.effects ⊆ ein.eval v.effects ∧
        ein.eval v.effects ⊆ {op} ∪ rest.eval v.effects ∧ op ∉ rest.eval v.effects ∧
        rest.eval v.effects ⊆ out.eval v.effects ∧ er.eval v.effects ⊆ out.eval v.effects := by
      simp [d, Constraints.handler, X.holds_conjunction, X.holds_top, X.holds_le, O.refl,
        Constraints.split, X.holds_and, X.holds_effectLe, X.holds_lacks,
        effect_eval_union, effect_eval_singleton, cq, and_assoc]
    have hdbs : (X.support db).Subset outer := (Names.subset_union_right _ _).trans hro
    have hdrs : (X.support dr).Subset outer := Names.subset_union_right _ _
    have avoid : X.Avoids d hidden := by
      apply X.avoids_of_transport
      intro v w hw hv
      have hwo : w.AgreeOn v outer :=
        ⟨fun i hi => (hw.1 i (fun hm => Finset.disjoint_left.mp hhidden.1 hm (hoc.1 hi))).symm,
          fun i hi => (hw.2 i (fun hm => Finset.disjoint_left.mp hhidden.2 hm (hoc.2 hi))).symm⟩
      obtain ⟨hb, hr', hcl, he⟩ := (shape v).mp hv
      apply (shape w).mpr
      refine ⟨(X.holds_support db w v (hwo.mono hdbs)).mpr hb,
        (X.holds_support dr w v (hwo.mono hdrs)).mpr hr',
        (X.holds_agreeOutside (X.clause_avoids_witnesses decl.bound hidden _) hw).mp hcl, ?_⟩
      simpa only [heval v w (hwo.mono hco) ein hein, heval v w (hwo.mono hco) er her,
        heval v w (hwo.mono hco) rest hrest, heval v w (hwo.mono hco) out hout] using he
    have hscope : decl.Scoped X d g input result ein er rest out hidden := by
      constructor
      · exact g.avoids_of_support_disjoint decl.bound (hrigid.mono_right (hgs.trans hco))
      · exact hrigid.mono_right ((hi.union hr).trans hco)
      · exact Finset.disjoint_left.mpr fun i hm he =>
          Finset.disjoint_left.mp hrigid.2 hm (hco.2 (hes he))
      · have hdecl : (((T.support decl.input).union (T.support decl.output)).union decl.bound).Subset cf :=
          (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
        exact hhidden.mono_right (((hgs.trans hco).trans hoc).union
          ((((hi.union hr).trans hco).trans hoc).union hdecl))
      · exact avoid
      · exact Finset.disjoint_left.mpr fun i hm he =>
          Finset.disjoint_left.mp hhidden.2 hm (hoc.2 (hco.2 (hes he)))
    have generated : Inference sig X N X.top g (.handle body op ret clause) result out d :=
      .handle hs hc fresh hscope hdb hdr hdc
    cases Option.some.inj heq
    exact .check generated

end EHMX.HMX
