import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkInnerKindInvariant
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkPassageInternal
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertices of the inner reclosing, by kind

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors.  The inner classifier by kind
(`IsNoncrossingClosedWalk.innerKindClass`) is a complete orbit classifier of the inner reclosed rotation.
* An adjacent passage `l` is represented by the retained dart `alpha w[l]`.  From a retained dart at a
  vertex with an adjacent passage, the reclosed rotation is old rotation until the first reversal.
* A vertex without adjacent passage is represented by any retained dart there.  Every passage at the
  vertex is short, so the reclosed rotation jumps over the free sector of a reversal `alpha w[l]` to
  `w[l+1]`, and the darts strictly inside are internal (`internal_sideFaces_of_short`).  So rotation
  reaches every retained dart at the vertex (`innerSameCycle_of_notAdj`).

* `IsNoncrossingClosedWalk.innerKindRep`, `innerKindClass_rep`, `innerKindRep_sameCycle`.
* `IsNoncrossingClosedWalk.innerKindVertexEquiv`, `inner_vertexCount_kind`.

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

/-- **Representatives of the inner vertices by kind.** -/
noncomputable def innerKindRep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    InnerKindIndex M w → KeptDart M (sideFaces M w)
  | Sum.inl c => Classical.choose c.2.2
  | Sum.inr i => ⟨M.alpha (w.get i.1), fun hint =>
      hw.faceOf_alpha_not_mem_of_mem hM (List.get_mem w i.1) hint.1⟩

theorem innerKindClass_rep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (i : InnerKindIndex M w) : hw.innerKindClass hM hsector (hw.innerKindRep hM i) = i := by
  rcases i with ⟨c, hc, hex⟩ | ⟨l, hl⟩
  · have hv : M.vertexOf (hw.innerKindRep hM (Sum.inl ⟨c, hc, hex⟩)).1 = c :=
      Classical.choose_spec hex
    have hA : ¬ AdjVertex M w (M.vertexOf (hw.innerKindRep hM (Sum.inl ⟨c, hc, hex⟩)).1) := by
      rw [hv]; exact hc
    rw [hw.innerKindClass_eq_inl hM hsector _ hA]
    exact congrArg Sum.inl (Subtype.ext hv)
  · have hA : AdjVertex M w (M.vertexOf (hw.innerKindRep hM (Sum.inr ⟨l, hl⟩)).1) := ⟨l, rfl, hl⟩
    exact hw.innerKindClass_eq_inr hM hsector _ hA hl (m := 0)
      (by rw [pow_zero, Perm.one_apply]; rfl) (fun j hj => absurd hj (Nat.not_lt_zero j))

/-- **At a vertex without adjacent passage, inner rotation reaches every retained dart.** -/
theorem innerSameCycle_of_notAdj (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    {c : M.Vertex} (hc : ¬ AdjVertex M w c) :
    ∀ (n : ℕ) (z x : KeptDart M (sideFaces M w)), M.vertexOf z.1 = c → (M.sigma ^ n) z.1 = x.1 →
      (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma.SameCycle z x := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z x hz hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero, Perm.one_apply] at hn
      rw [show x = z from (Subtype.ext hn).symm]
    have hvz : M.vertexOf ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma z).1 = c := by
      rw [hw.vertexOf_innerSigma hM z]; exact hz
    by_cases ha : M.alpha z.1 ∈ w
    · obtain ⟨l, hl⟩ := List.get_of_mem ha
      have hzl : z.1 = M.alpha (w.get l) := by rw [hl, M.alpha_involutive]
      have hnadj : ¬ PassageAdjacent M w l := fun hadj =>
        hc ⟨l, by rw [← hzl]; exact hz, hadj⟩
      obtain ⟨a, ha', hafree⟩ := (hsector l).resolve_right hnadj
      have hx : M.faceOf (M.alpha z.1) ∈ sideFaces M w := (hw.faceOf_alpha_mem_iff hM z.2).mpr ha
      have key : ∀ (d : M.Dart) (hd : d ∈ w), d = w.get l →
          w.next d hd = w.get (finRotate w.length l) := by
        rintro d hd rfl
        exact next_get_eq hw.nodup l
      have hsa : (M.sigma ^ a) z.1 = w.get (finRotate w.length l) := by rw [hzl]; exact ha'
      have hsz : ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma z).1 =
          (M.sigma ^ a) z.1 := by
        rw [reclosed_sigma_val_of_mem (hw.innerCycle hM) z hx, hw.innerCycle_boundaryPerm_val hM,
          hsa]
        exact key _ _ hl.symm
      have ha0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · rw [h, pow_zero, Perm.one_apply] at hsa
          exact absurd ha (hw.alpha_not_mem _ (by rw [hsa]; exact List.get_mem w _))
        · exact h
      rcases Nat.lt_or_ge n a with hna | hna
      · have hint := hw.internal_sideFaces_of_short hM (List.get_mem w l) hafree h0 hna
        rw [← hzl, hn] at hint
        exact absurd hint x.2
      rcases Nat.eq_or_lt_of_le hna with hna | hna
      · have hxz : (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma z = x :=
          Subtype.ext (by rw [hsz, hna]; exact hn)
        rw [← hxz]
        exact Perm.SameCycle.rfl.apply_right
      · have hn' : (M.sigma ^ (n - a))
            ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma z).1 = x.1 := by
          rw [hsz, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hna.le]
          exact hn
        exact (Perm.SameCycle.rfl.apply_right).trans (ih (n - a) (by omega) _ x hvz hn')
    · have hsz : ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma z).1 = M.sigma z.1 :=
        reclosed_sigma_val_of_notMem (hw.innerCycle hM) z
          (fun h => ha ((hw.faceOf_alpha_mem_iff hM z.2).mp h))
      have hn' : (M.sigma ^ (n - 1))
          ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma z).1 = x.1 := by
        rw [hsz, ← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel h0]
        exact hn
      exact (Perm.SameCycle.rfl.apply_right).trans (ih (n - 1) (by omega) _ x hvz hn')

/-- **Every retained inner dart is on the reclosed vertex of the representative of its class.** -/
theorem innerKindRep_sameCycle (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideFaces M w)) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma.SameCycle
      (hw.innerKindRep hM (hw.innerKindClass hM hsector x)) x := by
  by_cases hA : AdjVertex M w (M.vertexOf x.1)
  · obtain ⟨l, hadj, m, hml, hmin⟩ := hw.exists_first_adjacent hM hsector hA
    rw [hw.innerKindClass_eq_inr hM hsector x hA hadj hml hmin]
    have hrep : hw.innerKindRep hM (Sum.inr ⟨l, hadj⟩) =
        ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma ^ m) x :=
      Subtype.ext (by
        show M.alpha (w.get l) = (((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma ^ m) x).1
        rw [hw.innerSigma_pow_val hM x m hmin, hml])
    rw [hrep]
    exact Perm.sameCycle_pow_left.mpr (Perm.SameCycle.refl _ _)
  · rw [hw.innerKindClass_eq_inl hM hsector x hA]
    have hex : ∃ z : KeptDart M (sideFaces M w), M.vertexOf z.1 = M.vertexOf x.1 := ⟨x, rfl⟩
    have hyv : M.vertexOf (Classical.choose hex).1 = M.vertexOf x.1 := Classical.choose_spec hex
    obtain ⟨n, hn⟩ := ((M.vertexOf_eq_iff _ _).mp hyv).exists_nat_pow_eq
    exact hw.innerSameCycle_of_notAdj hM hsector hA n _ x hyv hn

/-- **The vertices of the inner reclosing, by kind.** -/
noncomputable def innerKindVertexEquiv (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).Vertex ≃ InnerKindIndex M w :=
  OrbitClassifier.orbitEquiv (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma
    (hw.innerKindClass hM hsector) (hw.innerKindRep hM) (hw.innerKindClass_sigma hM hsector)
    (hw.innerKindClass_rep hM hsector) (hw.innerKindRep_sameCycle hM hsector)

theorem inner_vertexCount_kind (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).vertexCount =
      Nat.card (InnerKindIndex M w) :=
  Nat.card_congr (hw.innerKindVertexEquiv hM hsector)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerKindClass_rep
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerSameCycle_of_notAdj
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerKindRep_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.inner_vertexCount_kind
