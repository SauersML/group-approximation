import GroupApproximation.GGT.KazhdanHypGQEightTableFormat
import GroupApproximation.GGT.KazhdanHypGirthEightNontrivial
import GroupApproximation.GGT.KazhdanHypGirthEightTorsionExtraction
import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface

/-!
# End-to-end assembly for a checked `W(8)` triangle table

The finite table checker supplies the two finite facts used by the endpoint:
`GirthEightChecks` and the identification of the presentation link with the
algebraic `W(8)` link.  The latter is fed to
`girthEightSDPChecks_of_linkIdentification`, so the Gram rows are the rows of
`wEightQuadrangleLinkData` reindexed along the checked link equivalence; no
enumeration of the 1170 signed link vertices occurs here.

The only non-finite hypotheses left in this assembly are the landed
van Kampen producers.  They are written explicitly below.  The cactus and
mirror hypotheses use the exact names consumed by
`KazhdanHypGirthEightTorsionExtraction`; the seam hypothesis is the exposed
pairing/Euler input consumed by the same extraction theorem.  Hyperbolicity is
obtained from kohyp's `girthEightHyperbolicity_of_diagramPrimitives`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace KazhdanHypSharpExistenceAssembly

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GirthEightTorsionExtraction

/-! ## The exact producer hypotheses -/

/-- Kohyp's five van Kampen producers, in the universal form consumed by
`girthEightHyperbolicity_of_diagramPrimitives`. -/
abbrev DiagramPrimitivesProducer : Prop :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Nonempty Generator) (_ : Fintype TriangleIndex)
    (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    GirthEightDiagramPrimitives T

/-- The exact cactus producer required by
`cactusPowerBoundaryFilling_of_baseCellDeletion`. -/
abbrev CactusBaseCellDeletionProducer : Prop :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    CactusBaseCellDeletionForPower T

/-- The exact mirror-pair deletion producer required by
`mirrorPairCutSupply_of_surgeryDeletion`. -/
abbrev PowerDiscMirrorPairDeletionProducer : Prop :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    PowerDiscMirrorPairDeletionSupply T

/-- The exact exposed-pairing/Euler producer required by the final seam step
of `presented_isPowerTorsionFree_of_combMapOperations`. -/
abbrev ExposedPairingEulerProducer : Prop :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n),
    ExposedPairingEulerInput T D

/-! ## Universal geometric consequences -/

/-- The three extraction producers yield the universal torsion-free residual.
The construction is deliberately through the named `ExtractionInputs`
consumer, so this assembly does not duplicate cactus, surgery, or seam code. -/
theorem girthEightTorsionFree_of_extractionProducers
    (cactus : CactusBaseCellDeletionProducer)
    (mirror : PowerDiscMirrorPairDeletionProducer)
    (seam : ExposedPairingEulerProducer) :
    GirthEightTorsionFree := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  exact presented_isPowerTorsionFree_of_combMapOperations hchecks {
    filling := cactus Generator TriangleIndex fg dg ft dt T
    mirrorDeletion := mirror Generator TriangleIndex fg dg ft dt T
    seam := fun g n D => seam Generator TriangleIndex fg dg ft dt T g n D }

/-- Kohyp's landed diagram primitive producer gives the universal
`GirthEightHyperbolicity` residual. -/
theorem girthEightHyperbolicity_of_diagramPrimitives
    (primitives : DiagramPrimitivesProducer) :
    GirthEightHyperbolicity :=
  GirthEightVKInterface.girthEightHyperbolicity_of_diagramPrimitives primitives

/-! ## Checked-table endpoint -/

/-- A Boolean-checked `W(8)` table closes the infinite, finitely presented,
torsion-free, hyperbolic Kazhdan endpoint.  The theorem has exactly the four
not-yet-landed producers as explicit hypotheses: kohyp's diagram primitives,
the cactus base-cell deletion, the power-disc mirror-pair deletion, and the
exposed pairing/Euler input.  The table checker and its two soundness theorems
are imported from `KazhdanHyp.GQEightTable` as the finite part of the API.
-/
theorem sharpExistence_of_checkedTable
    (diagramPrimitives : DiagramPrimitivesProducer)
    (cactus : CactusBaseCellDeletionProducer)
    (mirror : PowerDiscMirrorPairDeletionProducer)
    (seam : ExposedPairingEulerProducer) :
    ∀ T : GQEightTable.Table,
      GQEightTable.checkTable T = true →
        Hyperbolic.SharpExistence := by
  intro T hT
  have hgeom : GirthEightChecks T 9 :=
    GQEightTable.girthEightChecks_of_checkTable T hT
  have hlink : TriangleLinkIdentification T
      SymplecticQuadrangle.wEightQuadrangleLinkData :=
    GQEightTable.linkIdentification_of_checkTable T hT
  have hdeg : (9 : ℚ) =
      SymplecticQuadrangle.wEightQuadrangleLinkData.deg := by
    exact SymplecticQuadrangle.wEightQuadrangleLinkData_parameters.1.symm
  have hsdp0 := girthEightSDPChecks_of_linkIdentification
    T hgeom SymplecticQuadrangle.wEightQuadrangleLinkData hlink hdeg
  have hgap : hlink.reindexed.gapValue = (5 / 9 : ℚ) := by
    change (SymplecticQuadrangle.wEightQuadrangleLinkData.reindex
      hlink.vertexEquiv).gapValue = (5 / 9 : ℚ)
    rw [QuadrangleLinkData.reindex_gapValue]
    exact SymplecticQuadrangle.wEightQuadrangleLinkData_parameters.2
  have hsdp : GirthEightSDPChecks T 9 (5 / 9)
      hlink.reindexed.gramRow := by
    simpa [hgap] using hsdp0
  exact sharpExistence_of_girthEightChecks
    (girthEightTorsionFree_of_extractionProducers cactus mirror seam)
    (girthEightHyperbolicity_of_diagramPrimitives diagramPrimitives)
    T 9 hlink.reindexed.gramRow hgeom hsdp

/-! ## The `GQ(2,2)` non-spectral model -/

/-- Model test for every endpoint conjunct except property `(T)`: once the
torsion-free and hyperbolic inputs have the same shape at ko's transcribed
`GQ(2,2)` table, positivity supplies infiniteness and the finite presentation
instance supplies finite presentation.  No spectral claim is made, since the
`GQ(2,2)` gap is below `1/2`. -/
theorem gqTwo_nonT_conjuncts_model
    (htf : IsPowerTorsionFree
      (TriangularHodgeLayer.Presented GQTwoTable.triangles))
    (hhyp : Hyperbolic.IsHyperbolicGroup
      (TriangularHodgeLayer.Presented GQTwoTable.triangles)) :
    Infinite (TriangularHodgeLayer.Presented GQTwoTable.triangles) ∧
      Group.IsFinitelyPresented
        (TriangularHodgeLayer.Presented GQTwoTable.triangles) ∧
      IsPowerTorsionFree
        (TriangularHodgeLayer.Presented GQTwoTable.triangles) ∧
      Hyperbolic.IsHyperbolicGroup
        (TriangularHodgeLayer.Presented GQTwoTable.triangles) := by
  refine ⟨infinite_of_positive_of_torsionFree GQTwoTable.triangles
      GQTwoTable.positive htf, inferInstance, htf, hhyp⟩

end KazhdanHypSharpExistenceAssembly
end GGT
end GroupApproximation
