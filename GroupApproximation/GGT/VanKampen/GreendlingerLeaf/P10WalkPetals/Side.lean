import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10WalkPetals.Shared
import GroupApproximation.Meta.AxiomGuard

/-!
# The side of `B` is constant along an excursion of `c` away from `B`

Lane gl-infra-01 (infrastructure).  `B` is any list of darts (in applications a simple closed
walk, e.g. a minimal petal), `sideFaces M B` its side.

* `infraPetal_side_const`: along a chained run of darts not retained by `B` whose interior
  vertices are off `B`, the predicate `faceOf d ∈ sideFaces M B` is constant (cross each edge
  by `p10QM_side_alpha_iff`, rotate around each vertex by `p10QS_side_iff_of_not_onB`).
* `infraPetal_side_const_infix`: the same for a linear block of a closed walk `c`, i.e. between
  consecutive visits of `c` to `B`.
* `infraPetal_oneSided_excursion`: such a run lies entirely on or entirely off the side.
* `infraPetal_oneSided_of_block`: if `c.cycle = X ++ B ++ Z` and the excursion `Z ++ X` back to
  `B` avoids `B` in its interior, all darts of `c` off `B` lie on one side of `B`.  With
  `hblk := Or.inl ⟨X, Z, hXBZ⟩` this supplies `hin` of `p10QM_move_FF` or `hout` of
  `p10QM_move_TT`.

This is NOT the (false) dichotomy for a minimal petal: see the docstring of
`P10WalkPetals.Shared`.

All PROVED, unconditionally.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

section Side

/-- **The side is constant between visits to `B`.** -/
theorem infraPetal_side_const {M : CombMap.{v}} (B W : List M.Dart) :
    ∀ x : M.Dart, (x :: W).IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) →
      (∀ d ∈ x :: W, ¬walkKeep M B d) → (∀ e ∈ W, ¬p10QS_OnB M B (M.vertexOf e)) →
      ∀ e ∈ x :: W, (M.faceOf x ∈ sideFaces M B ↔ M.faceOf e ∈ sideFaces M B) := by
  induction W with
  | nil =>
    intro x _ _ _ e he
    rcases List.mem_singleton.mp he with rfl
    exact Iff.rfl
  | cons y W ih =>
    intro x hch hoff hW e he
    have hxy : M.vertexOf (M.alpha x) = M.vertexOf y := (List.isChain_cons_cons.mp hch).1
    have hk : ¬walkKeep M B x := hoff x List.mem_cons_self
    have hy : ¬p10QS_OnB M B (M.vertexOf (M.alpha x)) := by
      rw [hxy]
      exact hW y List.mem_cons_self
    have hstep : M.faceOf x ∈ sideFaces M B ↔ M.faceOf y ∈ sideFaces M B :=
      (p10QM_side_alpha_iff M B (d := x) (fun h => hk (Or.inl h))
        (fun h => hk (Or.inr h))).trans
        (p10QS_side_iff_of_not_onB M B hxy hy)
    rcases List.mem_cons.mp he with rfl | he'
    · exact Iff.rfl
    · exact hstep.trans (ih y (List.isChain_cons_cons.mp hch).2
        (fun d hd => hoff d (List.mem_cons_of_mem x hd))
        (fun e' he'' => hW e' (List.mem_cons_of_mem y he'')) e he')

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_side_const

/-- **The side is constant along a linear block of a closed walk** avoiding `B`. -/
theorem infraPetal_side_const_infix {M : CombMap.{v}} {c : List M.Dart} (B : List M.Dart)
    (hc : IsClosedDartWalk M c) {x : M.Dart} {W : List M.Dart} (hinf : x :: W <:+: c)
    (hoff : ∀ d ∈ x :: W, ¬walkKeep M B d) (hW : ∀ e ∈ W, ¬p10QS_OnB M B (M.vertexOf e)) :
    ∀ e ∈ x :: W, (M.faceOf x ∈ sideFaces M B ↔ M.faceOf e ∈ sideFaces M B) := by
  have hch : c.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) := by
    obtain ⟨-, h, -⟩ := hc
    exact h
  exact infraPetal_side_const B W x (hch.infix hinf) hoff hW

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_side_const_infix

/-- **An excursion away from `B` is one-sided.** -/
theorem infraPetal_oneSided_excursion {M : CombMap.{v}} (B W : List M.Dart)
    (hch : W.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e))
    (hoff : ∀ d ∈ W, ¬walkKeep M B d) (hW : ∀ e ∈ W.tail, ¬p10QS_OnB M B (M.vertexOf e)) :
    (∀ d ∈ W, M.faceOf d ∈ sideFaces M B) ∨ (∀ d ∈ W, M.faceOf d ∉ sideFaces M B) := by
  cases W with
  | nil =>
    refine Or.inl fun d hd => ?_
    simp at hd
  | cons x W =>
    have hconst := infraPetal_side_const B W x hch hoff hW
    by_cases hx : M.faceOf x ∈ sideFaces M B
    · exact Or.inl fun d hd => (hconst d hd).mp hx
    · exact Or.inr fun d hd h => hx ((hconst d hd).mpr h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_oneSided_excursion

/-- **One-sided criterion for a linear block `B` of a boundary cycle**: if the excursion
`Z ++ X` of `c` from the end of `B` back to its start meets `B` only at its two ends, every
dart of `c` off `B` is on the side of `B`, or every such dart is off it. -/
theorem infraPetal_oneSided_of_block {M : CombMap.{v}} {F : Finset M.Face}
    (c : BoundaryCycle M F) (hc : IsClosedDartWalk M c.cycle) {X B Z : List M.Dart}
    (hXBZ : c.cycle = X ++ B ++ Z)
    (hint : ∀ e ∈ (Z ++ X).tail, ¬p10QS_OnB M B (M.vertexOf e)) :
    (∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∈ sideFaces M B) ∨
      (∀ d ∈ c.cycle, d ∉ B → M.faceOf d ∉ sideFaces M B) := by
  have hnd : (X ++ B ++ Z).Nodup := by
    rw [← hXBZ]
    exact c.cycle_nodup
  have hrot : IsClosedDartWalk M (B ++ Z ++ X) :=
    IsClosedDartWalk.append_comm (P := X) (Q := B ++ Z)
      (by rw [← List.append_assoc, ← hXBZ]; exact hc)
  have hch : (Z ++ X).IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) := by
    obtain ⟨-, h, -⟩ := hrot
    rw [List.append_assoc] at h
    exact (List.isChain_append.mp h).2.1
  have hmem : ∀ d ∈ Z ++ X, d ∈ c.cycle := fun d hd => by
    rw [hXBZ]
    exact p10QM_mem_outer (p10QM_mem_swap hd)
  have hoff : ∀ d ∈ Z ++ X, ¬walkKeep M B d := by
    intro d hd hk
    rcases hk with h | h
    · exact p10QM_not_mem_mid hnd (p10QM_mem_swap hd) h
    · refine p10QM_alpha_not_mem M c (hmem d hd) ?_
      rw [hXBZ]
      exact p10QM_mem_mid h
  have hback : ∀ d ∈ c.cycle, d ∉ B → d ∈ Z ++ X := fun d hd hdB => by
    rw [hXBZ] at hd
    exact p10QM_mem_swap (p10QM_mem_outer_of_not_mem hd hdB)
  rcases infraPetal_oneSided_excursion B (Z ++ X) hch hoff hint with h | h
  · exact Or.inl fun d hd hdB => h d (hback d hd hdB)
  · exact Or.inr fun d hd hdB => h d (hback d hd hdB)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_oneSided_of_block

end Side

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
