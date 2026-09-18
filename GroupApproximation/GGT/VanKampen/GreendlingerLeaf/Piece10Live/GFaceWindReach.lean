import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: the invariant along excision sequences

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-55.

* `gfaceWind_step_inv`: one excision step (`Piece10Live/GFaceWindStep`) keeps the invariant
  `gfaceWind_Inv` and shortens the walk.
* `gfaceWind_reach_inv`, `gfaceWind_reach_pair`: so does any nonempty sequence of steps.

## Truth check

See `Piece10Live/GFaceWind`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open GFaceChoose
open scoped Classical

/-- **One step keeps the invariant**: on a duplicate-free walk `C` of a planar map, an excision
step from a state satisfying the invariant reaches a state satisfying it, with a shorter walk. -/
theorem gfaceWind_step_inv {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    (hC : C.Nodup) {o : M.Face} {s t : List M.Dart × (M.Face → ℤ)}
    (hs : gfaceWind_Inv M C o s.1 s.2) (h : gfaceWind_Step M o s t) :
    gfaceWind_Inv M C o t.1 t.2 ∧ t.1.length < s.1.length := by
  obtain ⟨hfil, hch, hcob, ho⟩ := hs
  obtain ⟨p, A, q, hseg, hstep⟩ := h
  have hnd : (p ++ A ++ q).Nodup := by
    have h0 := List.Nodup.filter (gfaceWind_mem s.1) hC
    rw [hfil, hseg] at h0
    exact h0
  rw [hseg] at hfil hch hcob
  obtain ⟨hpA', -, hq⟩ := List.nodup_append.mp hnd
  obtain ⟨-, -, hpA⟩ := List.nodup_append.mp hpA'
  have hApq : ∀ x ∈ A, x ∉ p ++ q := by
    intro x hxA hx
    rcases List.mem_append.mp hx with hxp | hxq
    · exact hpA x hxp x hxA rfl
    · exact hq x (List.mem_append_right p hxA) x hxq rfl
  have hqpA : ∀ x ∈ q ++ p, x ∉ A := by
    intro x hx hxA
    refine hApq x hxA ?_
    rcases List.mem_append.mp hx with hxq | hxp
    · exact List.mem_append_right p hxq
    · exact List.mem_append_left q hxp
  have hmem1 : ∀ x, x ∈ p ++ A ++ q ↔ x ∈ A ∨ x ∈ p ++ q := by
    intro x
    simp only [List.mem_append]
    tauto
  have hmem2 : ∀ x, x ∈ p ++ A ++ q ↔ x ∈ q ++ p ∨ x ∈ A := by
    intro x
    simp only [List.mem_append]
    tauto
  rcases hstep with ⟨hw, ht1, ht2⟩ | ⟨hw, ht1, ht2⟩
  · obtain ⟨hcob', ho'⟩ := gfaceWind_cob_excise hM hw hmem1 hApq hcob ho ht2
    have hsub : ∀ x ∈ p ++ q, x ∈ p ++ A ++ q := fun x hx => (hmem1 x).mpr (Or.inr hx)
    have hpos := List.length_pos_iff.mpr hw.ne_nil
    rw [ht1, hseg]
    refine ⟨⟨?_, gfaceChoose_chain_cut hw.ne_nil hw.closes hch, hcob', ho'⟩, ?_⟩
    · rw [gfaceWind_filter_sub hfil hsub]
      exact gfaceChoose_filter_cut hnd fun x hx => gfaceWind_mem_eq_true_iff.trans
        ⟨fun h hA => hApq x hA h, fun h => ((hmem1 x).mp hx).resolve_left h⟩
    · simp only [List.length_append]
      omega
  · obtain ⟨hcob', ho'⟩ := gfaceWind_cob_excise hM hw hmem2 hqpA hcob ho ht2
    have hsub : ∀ x ∈ A, x ∈ p ++ A ++ q := fun x hx => (hmem2 x).mpr (Or.inr hx)
    have hpos := List.length_pos_iff.mpr hw.ne_nil
    rw [ht1, hseg]
    refine ⟨⟨?_, hch.left_of_append.right_of_append, hcob', ho'⟩, ?_⟩
    · rw [gfaceWind_filter_sub hfil hsub]
      exact gfaceChoose_filter_keep hnd fun _ => gfaceWind_mem_eq_true_iff
    · simp only [List.length_append] at hpos ⊢
      omega

/-- **Excision sequences keep the invariant**, and shorten the walk. -/
theorem gfaceWind_reach_inv {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    (hC : C.Nodup) {o : M.Face} {s t : List M.Dart × (M.Face → ℤ)}
    (h : Relation.TransGen (gfaceWind_Step M o) s t) :
    gfaceWind_Inv M C o s.1 s.2 → gfaceWind_Inv M C o t.1 t.2 ∧ t.1.length < s.1.length := by
  induction h with
  | single hst => exact fun hs => gfaceWind_step_inv hM hC hs hst
  | tail _ hst ih =>
    intro hs
    obtain ⟨h1, h2⟩ := ih hs
    obtain ⟨h3, h4⟩ := gfaceWind_step_inv hM hC h1 hst
    exact ⟨h3, lt_trans h4 h2⟩

/-- **Excision sequences keep the invariant**, on explicit pairs. -/
theorem gfaceWind_reach_pair {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    (hC : C.Nodup) {o : M.Face} {c c' : List M.Dart} {g g' : M.Face → ℤ}
    (h : Relation.TransGen (gfaceWind_Step M o) (c, g) (c', g'))
    (hs : gfaceWind_Inv M C o c g) : gfaceWind_Inv M C o c' g' ∧ c'.length < c.length :=
  gfaceWind_reach_inv hM hC h hs

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_step_inv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_reach_inv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_reach_pair
