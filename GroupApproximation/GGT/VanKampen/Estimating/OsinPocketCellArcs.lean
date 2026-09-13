import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.Meta.AxiomGuard

/-!
# Arcs of relator cells on the boundary of a pocket

Osin, *Small cancellations over relatively hyperbolic groups and embedding theorems*,
arXiv:math/0411039v3, §9, proof of Lemma 9.7.  When two distinct contiguity regions join the
same two cells, the proof cuts out the subdiagram `Ξ` with `∂Ξ = s_1 t_1 s_2 t_2`, where `s_1`,
`s_2` are sides of the two regions and `t_1`, `t_2` are arcs of the two cells.  On the boundary
of the face set of `Ξ` an arc of a cell is crossed by `alpha` and read in reverse order, so a
cell part of that boundary is `invDarts Δ A.darts` for a cyclic arc `A` of `cellDarts Δ i`.
A side part is a side of a region crossed by `alpha` in the same way.

This module proves the word-level half of that step:

* `CyclicArc.dartWord_darts_cellDarts`: the word on an arc of a cell is a prefix of a cyclic
  permutation of the cell's relator word;
* `CyclicArc.dartWord_invDarts_darts_cellDarts`: the reversed arc reads the formal inverse of
  that prefix;
* `CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts` and
  `CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts`: under `C(ε, μ, λ, c, ρ)` both
  readings are `(λ, c)`-quasi-geodesic, which is what the four-section cut asks of `t_1` and
  `t_2`;
* `CyclicArc.rest` and `CyclicArc.rotated_eq_darts_append_rest_darts`: the complementary arc,
  which starts where the arc ends, so that the rotated carrier is the arc followed by it;
* `ContiguityGeometry.invDarts_rightSide_length_le` and `invDarts_leftSide_length_le`: a side
  crossed by `alpha` still has length at most `ε`, which is what the cut asks of `s_1` and `s_2`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open GroupApproximation.HullSC

universe u w v

namespace CyclicArc

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}

/-- The reversed arc is `invDarts` of the arc. -/
theorem invDarts_darts {Delta : DiscDiagram.{u, w, v} W} {cycle : List Delta.toCombMap.Dart}
    (arc : CyclicArc cycle) : invDarts Delta arc.darts = arc.reverseDarts :=
  rfl

/-- The word on an arc of a relator cell is a prefix of a cyclic permutation of the cell's
relator word. -/
theorem dartWord_darts_cellDarts {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (arc : CyclicArc (cellDarts Delta i)) :
    dartWord Delta arc.darts = ((cell Delta i).word.rotate arc.start.1).take arc.length := by
  rw [darts, rotated_eq_rotate, ← dartWord_cellDarts Delta i]
  simp only [dartWord, List.map_take, List.map_rotate]

/-- Reading an arc of a relator cell backwards gives the formal inverse of a prefix of a cyclic
permutation of the cell's relator word. -/
theorem dartWord_invDarts_darts_cellDarts {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount} (arc : CyclicArc (cellDarts Delta i)) :
    dartWord Delta (invDarts Delta arc.darts) =
      RelWord.revInv (((cell Delta i).word.rotate arc.start.1).take arc.length) := by
  rw [invDarts, dartWord_reverse_alpha, dartWord_darts_cellDarts]

/-- Under `C(ε, μ, λ, c, ρ)`, the word on an arc of a relator cell is
`(λ, c)`-quasi-geodesic. -/
theorem isLambdaCQuasiGeodesicWord_darts_cellDarts {D : GGT.RelGenSet G Lambda}
    {eps rho : ℕ} {mu lambda c : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (arc : CyclicArc (cellDarts Delta i)) :
    IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta arc.darts) := by
  rw [dartWord_darts_cellDarts]
  exact CutSections.isLambdaCQuasiGeodesicWord_rotate_take hcond (cell Delta i).word_mem _ _

/-- Under `C(ε, μ, λ, c, ρ)`, an arc of a relator cell read backwards is
`(λ, c)`-quasi-geodesic.  This is the reading of a cell part of a pocket boundary. -/
theorem isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts {D : GGT.RelGenSet G Lambda}
    {eps rho : ℕ} {mu lambda c : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (arc : CyclicArc (cellDarts Delta i)) :
    IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta (invDarts Delta arc.darts)) := by
  rw [dartWord_invDarts_darts_cellDarts]
  exact CutSections.isLambdaCQuasiGeodesicWord_revInv_rotate_take hcond (cell Delta i).word_mem _ _

/-- The complementary arc: the rest of the carrier cycle, starting where the arc ends. -/
def rest {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) : CyclicArc cycle where
  start := ⟨(arc.start.1 + arc.length) % cycle.length, by
    rcases Nat.eq_zero_or_pos cycle.length with h | h
    · have hs := arc.start.2
      have hl := arc.length_le
      exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    · exact Nat.lt_succ_of_lt (Nat.mod_lt _ h)⟩
  length := cycle.length - arc.length
  length_le := Nat.sub_le _ _

/-- The complementary arc has the remaining length. -/
theorem rest_length {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) :
    arc.rest.length = cycle.length - arc.length :=
  rfl

/-- The carrier rotated to the start of an arc is the arc followed by its complementary arc. -/
theorem rotated_eq_darts_append_rest_darts {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) : arc.rotated = arc.darts ++ arc.rest.darts := by
  have hrest : arc.rest.rotated = arc.rotated.rotate arc.length := by
    rw [arc.rest.rotated_eq_rotate, arc.rotated_eq_rotate, List.rotate_rotate]
    exact List.rotate_mod cycle _
  have hL : arc.length ≤ arc.rotated.length := by
    rw [arc.rotated_length]
    exact arc.length_le
  have hdrop : arc.rest.darts = arc.rotated.drop arc.length := by
    rw [darts, hrest, List.rotate_eq_drop_append_take hL]
    exact List.take_left' (by rw [List.length_drop, arc.rotated_length, rest_length])
  rw [hdrop, darts, List.take_append_drop]

end CyclicArc

namespace ContiguityGeometry

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))} {D : GGT.RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}

/-- The right side crossed by `alpha` has length at most `ε`. -/
theorem invDarts_rightSide_length_le (H : ContiguityGeometry D eps Delta faces) :
    (invDarts Delta H.rightSide).length ≤ eps := by
  rw [invDarts, List.length_map, List.length_reverse]
  exact H.rightSide_length_le

/-- The left side crossed by `alpha` has length at most `ε`. -/
theorem invDarts_leftSide_length_le (H : ContiguityGeometry D eps Delta faces) :
    (invDarts Delta H.leftSide).length ≤ eps := by
  rw [invDarts, List.length_map, List.length_reverse]
  exact H.leftSide_length_le

end ContiguityGeometry

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.invDarts_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.dartWord_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.dartWord_invDarts_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.rest
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.rest_length
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.rotated_eq_darts_append_rest_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.invDarts_rightSide_length_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.invDarts_leftSide_length_le
