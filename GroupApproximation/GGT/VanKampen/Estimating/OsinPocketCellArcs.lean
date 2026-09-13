import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
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

This module proves the word-level half of that step:

* `CyclicArc.dartWord_darts_cellDarts`: the word on an arc of a cell is a prefix of a cyclic
  permutation of the cell's relator word;
* `CyclicArc.dartWord_invDarts_darts_cellDarts`: the reversed arc reads the formal inverse of
  that prefix;
* `CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts` and
  `CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts`: under `C(ε, μ, λ, c, ρ)` both
  readings are `(λ, c)`-quasi-geodesic, which is what the four-section cut asks of `t_1` and
  `t_2`.

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

end CyclicArc

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.invDarts_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.dartWord_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.dartWord_invDarts_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts
