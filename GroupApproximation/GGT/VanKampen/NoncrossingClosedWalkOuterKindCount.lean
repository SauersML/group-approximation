import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkOuterKindInvariant
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkPassageInternalOuter
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertices of the outer reclosing, by kind

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors.  The outer classifier by kind
(`IsNoncrossingClosedWalk.outerKindClass`) is a complete orbit classifier of the outer reclosed rotation.
* A passage `l` that is not adjacent is represented by the retained dart `w[l+1]`.  From a retained dart
  at a touched vertex without adjacent passage, the reclosed rotation is old rotation until the first
  walk dart.
* An untouched vertex, or a vertex with an adjacent passage, is represented by any retained dart there.
  Every passage at the vertex is adjacent, so the reclosed rotation jumps over the free sector from
  `w[l+1]` to `alpha w[l]`, and the darts strictly inside are internal
  (`internal_sideOutside_of_free`).  So rotation reaches every retained dart at the vertex
  (`outerSameCycle_of_notShort`).

* `IsNoncrossingClosedWalk.outerKindRep`, `outerKindClass_rep`, `outerKindRep_sameCycle`.
* `IsNoncrossingClosedWalk.outerKindVertexEquiv`, `outer_vertexCount_kind`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides SectorNoninterleaving NoncrossingClosedWalkEuler

universe u

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Representatives of the outer vertices by kind.** -/
noncomputable def outerKindRep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    OuterKindIndex M w → KeptDart M (sideOutside M w)
  | Sum.inl c => Classical.choose c.2.2
  | Sum.inr i => ⟨w.get (finRotate w.length i.1), fun hint => (mem_sideOutside_iff M w _).mp hint.1
      ((hw.isBoundaryDart_sideFaces_iff hM _).mpr (List.get_mem w _)).1⟩

theorem outerKindClass_rep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (i : OuterKindIndex M w) : hw.outerKindClass (hw.outerKindRep hM i) = i := by
  rcases i with ⟨c, hc, hex⟩ | ⟨l, hl⟩
  · have hv : M.vertexOf (hw.outerKindRep hM (Sum.inl ⟨c, hc, hex⟩)).1 = c :=
      Classical.choose_spec hex
    have hS : ¬ (Touched M w (M.vertexOf (hw.outerKindRep hM (Sum.inl ⟨c, hc, hex⟩)).1) ∧
        ¬ AdjVertex M w (M.vertexOf (hw.outerKindRep hM (Sum.inl ⟨c, hc, hex⟩)).1)) := by
      rw [hv]
      rintro ⟨hT, hA⟩
      rcases hc with hc | hc
      · exact hc hT
      · exact hA hc
    rw [hw.outerKindClass_eq_inl _ hS]
    exact congrArg Sum.inl (Subtype.ext hv)
  · have hvl : M.vertexOf (hw.outerKindRep hM (Sum.inr ⟨l, hl⟩)).1 =
        M.vertexOf (M.alpha (w.get l)) :=
      (get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes l).symm
    have hS : Touched M w (M.vertexOf (hw.outerKindRep hM (Sum.inr ⟨l, hl⟩)).1) ∧
        ¬ AdjVertex M w (M.vertexOf (hw.outerKindRep hM (Sum.inr ⟨l, hl⟩)).1) := by
      rw [hvl]
      refine ⟨⟨l, rfl⟩, fun hA => ?_⟩
      obtain ⟨j, hj, hadj⟩ := hA
      exact hl (hw.passageAdjacent_of_vertex hM hsector hadj hj.symm)
    exact hw.outerKindClass_eq_inr _ hS hl (m := 0)
      (by rw [pow_zero, Perm.one_apply]; rfl) (fun j hj => absurd hj (Nat.not_lt_zero j))

/-- **At an untouched vertex or a vertex with an adjacent passage, outer rotation reaches every
retained dart.** -/
theorem outerSameCycle_of_notShort (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    {c : M.Vertex} (hc : ¬ (Touched M w c ∧ ¬ AdjVertex M w c)) :
    ∀ (n : ℕ) (z x : KeptDart M (sideOutside M w)), M.vertexOf z.1 = c → (M.sigma ^ n) z.1 = x.1 →
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma.SameCycle z x := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z x hz hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero, Perm.one_apply] at hn
      rw [show x = z from (Subtype.ext hn).symm]
    have hvz : M.vertexOf ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma z).1 = c := by
      rw [hw.vertexOf_outerSigma hM z]; exact hz
    by_cases hzw : z.1 ∈ w
    · obtain ⟨p, hp⟩ := List.get_of_mem hzw
      obtain ⟨l, hzl⟩ : ∃ l : Fin w.length, z.1 = w.get (finRotate w.length l) :=
        ⟨(finRotate w.length).symm p, by rw [Equiv.apply_symm_apply, hp]⟩
      have hvl : M.vertexOf (M.alpha (w.get l)) = c := by
        rw [get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes, ← hzl]; exact hz
      have hA : AdjVertex M w c := by
        by_contra hA
        exact hc ⟨⟨l, hvl⟩, hA⟩
      obtain ⟨i, hi, hadji⟩ := hA
      have hadj : PassageAdjacent M w l :=
        hw.passageAdjacent_of_vertex hM hsector hadji (hvl.trans hi.symm)
      obtain ⟨b, hb, hbfree⟩ := id hadj
      have hx : M.faceOf (M.alpha z.1) ∈ sideOutside M w :=
        (hw.faceOf_alpha_mem_sideOutside_iff hM z.2).mpr hzw
      have key : ∀ (d : M.Dart) (hd : d ∈ w), d = w.get (finRotate w.length l) →
          M.alpha (w.prev d hd) = M.alpha (w.get l) := by
        rintro d hd rfl
        rw [prev_get_finRotate hw.nodup l hd]
      have hsb : (M.sigma ^ b) z.1 = M.alpha (w.get l) := by rw [hzl]; exact hb
      have hsz : ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma z).1 =
          (M.sigma ^ b) z.1 := by
        rw [reclosed_sigma_val_of_mem (hw.outerCycle hM) z hx, hw.outerCycle_boundaryPerm_val hM,
          hsb]
        exact key _ _ (by
          show M.alpha (M.alpha z.1) = w.get (finRotate w.length l)
          rw [M.alpha_involutive]; exact hzl)
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · rw [h, pow_zero, Perm.one_apply] at hb
          exact absurd (by rw [← hb]; exact List.get_mem w _)
            (hw.alpha_not_mem _ (List.get_mem w l))
        · exact h
      rcases Nat.lt_or_ge n b with hnb | hnb
      · have hint := hw.internal_sideOutside_of_free hM (List.get_mem w (finRotate w.length l))
          hbfree h0 hnb
        rw [← hzl, hn] at hint
        exact absurd hint x.2
      rcases Nat.eq_or_lt_of_le hnb with hnb | hnb
      · have hxz : (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma z = x :=
          Subtype.ext (by rw [hsz, hnb]; exact hn)
        rw [← hxz]
        exact Perm.SameCycle.rfl.apply_right
      · have hn' : (M.sigma ^ (n - b))
            ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma z).1 = x.1 := by
          rw [hsz, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hnb.le]
          exact hn
        exact (Perm.SameCycle.rfl.apply_right).trans (ih (n - b) (by omega) _ x hvz hn')
    · have hsz : ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma z).1 = M.sigma z.1 :=
        reclosed_sigma_val_of_notMem (hw.outerCycle hM) z
          (fun h => hzw ((hw.faceOf_alpha_mem_sideOutside_iff hM z.2).mp h))
      have hn' : (M.sigma ^ (n - 1))
          ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma z).1 = x.1 := by
        rw [hsz, ← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel h0]
        exact hn
      exact (Perm.SameCycle.rfl.apply_right).trans (ih (n - 1) (by omega) _ x hvz hn')

/-- **Every retained outer dart is on the reclosed vertex of the representative of its class.** -/
theorem outerKindRep_sameCycle (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideOutside M w)) :
    (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma.SameCycle
      (hw.outerKindRep hM (hw.outerKindClass x)) x := by
  by_cases hS : Touched M w (M.vertexOf x.1) ∧ ¬ AdjVertex M w (M.vertexOf x.1)
  · obtain ⟨l, hl, m, hml, hmin⟩ := hw.exists_first_short hS.1 hS.2
    rw [hw.outerKindClass_eq_inr x hS hl hml hmin]
    have hrep : hw.outerKindRep hM (Sum.inr ⟨l, hl⟩) =
        ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma ^ m) x :=
      Subtype.ext (by
        show w.get (finRotate w.length l) =
          (((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma ^ m) x).1
        rw [hw.outerSigma_pow_val hM x m hmin, hml])
    rw [hrep]
    exact Perm.sameCycle_pow_left.mpr (Perm.SameCycle.refl _ _)
  · rw [hw.outerKindClass_eq_inl x hS]
    have hex : ∃ z : KeptDart M (sideOutside M w), M.vertexOf z.1 = M.vertexOf x.1 := ⟨x, rfl⟩
    have hyv : M.vertexOf (Classical.choose hex).1 = M.vertexOf x.1 := Classical.choose_spec hex
    obtain ⟨n, hn⟩ := ((M.vertexOf_eq_iff _ _).mp hyv).exists_nat_pow_eq
    exact hw.outerSameCycle_of_notShort hM hsector hS n _ x hyv hn

/-- **The vertices of the outer reclosing, by kind.** -/
noncomputable def outerKindVertexEquiv (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).Vertex ≃ OuterKindIndex M w :=
  OrbitClassifier.orbitEquiv (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma
    hw.outerKindClass (hw.outerKindRep hM) (hw.outerKindClass_sigma hM hsector)
    (hw.outerKindClass_rep hM hsector) (hw.outerKindRep_sameCycle hM hsector)

theorem outer_vertexCount_kind (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).vertexCount =
      Nat.card (OuterKindIndex M w) :=
  Nat.card_congr (hw.outerKindVertexEquiv hM hsector)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerKindClass_rep
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerSameCycle_of_notShort
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerKindRep_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outer_vertexCount_kind
