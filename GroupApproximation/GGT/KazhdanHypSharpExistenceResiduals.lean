import GroupApproximation.GGT.KazhdanHypSharpExistenceAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The checked-table endpoint over the two universal residuals

`KazhdanHypSharpExistenceAssembly.sharpExistence_of_checkedTable` takes, among
its hypotheses, `DiagramPrimitivesProducer`: a `GirthEightDiagramPrimitives T`
for every finite triangle table.  That record is too strong to be a producer
target, for a reason visible in its `successiveStars` field alone.

## The `successiveStars` field demands `0`-slim triangles

`SuccessiveStarLayers T` carries a diagram with `TriangularDiagramLocalData`
and four inequalities which, at a table passing `GirthEightChecks`, contradict
the proved area bound `innerFaceCount + 8 ≤ 3 * boundaryLength`
(`GirthEightSlim.not_girthEight_layers_of_depth_gt`).  The record mentions no
point of the geodesic triangle it is produced from, so at a checked table the
field `successiveStars delta` is equivalent to the statement that no point is
`delta`-far from the two other sides, and the field quantifies over **every**
`delta`, `0` included.  `isSlimTriangles_zero_of_diagramPrimitives` below
proves the consequence: the record forces `0`-slim triangles in the Cayley
graph of every checked table.

That is false for the groups the record is meant for.  At an interior vertex
the eight triangles about a link octagon give neighbours `a`, `b⁻¹`, `c` of the
identity with `a` adjacent to `b⁻¹`, `b⁻¹` adjacent to `c`, and `a` not adjacent
to `c` (a three-cycle through `a` and `c` would bound a single relator cell,
whose letters all have one sign); the identity lies between `a` and `c` and
between neither pair of adjacent endpoints.  The slim-triangle consumer
`GirthEightSlim.presented_isHyperbolicGroup_of_girthEight_layer_construction`
needs the construction at ONE `delta`, chosen by the caller, and the
Bridson--Haefliger / Papasoglu argument supplies it only for large `delta`.

## What this module provides instead

`sharpExistence_of_checkedTable_of_residuals` is the same endpoint with the
two universal residuals of `GGT/KazhdanHypGirthEight.lean` as hypotheses:
`GirthEightHyperbolicity` and `GirthEightTorsionFree`.  Each is a true
statement about checked tables, and neither asks for more than the argument
gives.  Its proof is the proof of `sharpExistence_of_checkedTable` with the two
residuals inserted where the producers were consumed; the finite table
checker, the `W(8)` link identification, the exact `5/9` gap and Garland's
certificate are untouched.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace KazhdanHypSharpExistenceResiduals

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GirthEightPrimitives2
open GirthEightTorsionExtraction
open KazhdanHypSharpExistenceAssembly

/-! ## The contract diagnosis -/

/-- **The `successiveStars` field forces `0`-slim triangles.**  At a table
passing `GirthEightChecks`, every successive-star record is contradicted by the
linear area bound, and the field is asked at `delta = 0`; so no point of a side
lies off both other sides. -/
theorem isSlimTriangles_zero_of_diagramPrimitives
    {Generator TriangleIndex : Type}
    [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : GirthEightChecks T d) (P : GirthEightDiagramPrimitives T) :
    Hyperbolic.IsSlimTriangles
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) 0 := by
  apply GirthEightSlim.isSlimTriangles_of_girthEight_layer_construction
    (delta := 0) (Base := FreeGroup Generator) (Lambda := PEmpty)
    (W := triangleRelatorWords T)
  intro x y z p hp hfarXZ hfarZY
  let L := P.successiveStars 0 x y z p hp hfarXZ hfarZY
  exact ⟨L.diagram, L.localData.toTriangularGirthEightDiagram hchecks,
    L.depth, L.scale, L.loss, L.perimeter, L.layer, L.boundary_bound,
    L.layer_disjoint, L.layer_covers, L.depth_too_large⟩

/-- **The universal producer forces `0`-slim triangles at every checked
table.**  So `DiagramPrimitivesProducer` asserts that the Cayley graph of every
checked triangular presentation has `0`-slim geodesic triangles. -/
theorem isSlimTriangles_zero_of_diagramPrimitivesProducer
    (primitives : DiagramPrimitivesProducer) :
    ∀ (Generator TriangleIndex : Type)
      (_ : Fintype Generator) (_ : DecidableEq Generator)
      (_ : Nonempty Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
      GirthEightChecks T d →
      Hyperbolic.IsSlimTriangles
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) 0 := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  exact isSlimTriangles_zero_of_diagramPrimitives hchecks
    (primitives Generator TriangleIndex fg dg ng ft dt T)

/-! ## The endpoint over the two residuals -/

/-- **A Boolean-checked `W(8)` table closes `SharpExistence` from the two
universal girth-eight residuals.**  The same proof as
`sharpExistence_of_checkedTable`, with `GirthEightTorsionFree` and
`GirthEightHyperbolicity` in place of the four producers. -/
theorem sharpExistence_of_checkedTable_of_residuals
    (hyperbolicity : GirthEightHyperbolicity)
    (torsionFree : GirthEightTorsionFree) :
    ∀ (m : ℕ) (T : GQEightTableFormat.W8Table m),
      GQEightTableFormat.checkTable T.toTable = true →
        Hyperbolic.SharpExistence := by
  intro m T hT
  have hgeom : GirthEightChecks (GQEightTableFormat.triangles T.toTable) 9 :=
    GQEightTableFormat.girthEightChecks_of_checkTable T.toTable hT
  have hlink : TriangleLinkIdentification
      (GQEightTableFormat.triangles T.toTable)
      SymplecticQuadrangle.wEightQuadrangleLinkData :=
    GQEightTableFormat.linkIdentification_of_checkTable T hT
  have hdeg : (9 : ℚ) =
      SymplecticQuadrangle.wEightQuadrangleLinkData.deg := by
    exact SymplecticQuadrangle.wEightQuadrangleLinkData_parameters.1.symm
  have hsdp0 := girthEightSDPChecks_of_linkIdentification
    (GQEightTableFormat.triangles T.toTable) hgeom
    SymplecticQuadrangle.wEightQuadrangleLinkData hlink hdeg
  have hgap : hlink.reindexed.gapValue = (5 / 9 : ℚ) := by
    change (SymplecticQuadrangle.wEightQuadrangleLinkData.reindex
      hlink.vertexEquiv).gapValue = (5 / 9 : ℚ)
    rw [QuadrangleLinkData.reindex_gapValue]
    exact SymplecticQuadrangle.wEightQuadrangleLinkData_parameters.2
  rw [hgap] at hsdp0
  have htf : IsPowerTorsionFree
      (TriangularHodgeLayer.Presented
        (GQEightTableFormat.triangles T.toTable)) :=
    torsionFree _ _ inferInstance inferInstance inferInstance inferInstance
      inferInstance (GQEightTableFormat.triangles T.toTable) 9 hgeom
  have hready := infinite_and_finitelyPresented_of_girthEightChecks hgeom htf
  have hhyp : Hyperbolic.IsHyperbolicGroup
      (TriangularHodgeLayer.Presented
        (GQEightTableFormat.triangles T.toTable)) :=
    hyperbolicity _ _ inferInstance inferInstance inferInstance inferInstance
      inferInstance (GQEightTableFormat.triangles T.toTable) 9 hgeom
  exact ⟨TriangularHodgeLayer.Presented
      (GQEightTableFormat.triangles T.toTable), inferInstance,
    hready.1, hready.2, htf, hhyp,
    hasKazhdanPropertyT_of_girthEightSDPChecks hgeom hsdp0⟩

end KazhdanHypSharpExistenceResiduals
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypSharpExistenceResiduals.isSlimTriangles_zero_of_diagramPrimitives
#audit_axioms GroupApproximation.GGT.KazhdanHypSharpExistenceResiduals.isSlimTriangles_zero_of_diagramPrimitivesProducer
#audit_axioms GroupApproximation.GGT.KazhdanHypSharpExistenceResiduals.sharpExistence_of_checkedTable_of_residuals
