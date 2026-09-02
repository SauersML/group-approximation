import GroupApproximation.GGT.KazhdanHypGQLinkTransfer
import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleStrongRegular

/-!
# The W(8) certificate endpoint

The algebraic symplectic quadrangle supplies degree nine and normalized gap
`5/9`.  This file specializes the generic link-transfer theorem to that
quadrangle, so a concrete triangle table only has to provide its girth-eight
checks and a link identification.
-/

namespace GroupApproximation
namespace KazhdanHyp

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator] [Nonempty Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The W(8) association scheme transported to the signed-generator type. -/
noncomputable def wEightReindexed
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (I : TriangleLinkIdentification T
      GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData) :
    QuadrangleLinkData (Generator × Bool) :=
  QuadrangleLinkData.reindex
    GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData
    I.vertexEquiv

/-- A degree-nine triangle table identified with the algebraic W(8) link has
the exact rational SDP certificate with gap `5/9`. -/
theorem girthEightSDPChecks_of_wEightLinkIdentification
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hgeom : GirthEightChecks T 9)
    (I : TriangleLinkIdentification T
      GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData) :
    GirthEightSDPChecks T 9 (5 / 9 : ℚ)
      ((wEightReindexed I).gramRow :
        QuadRow (Generator × Bool) → Generator × Bool → ℚ) := by
  have hparams :=
    GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData_parameters
  have hdeg : (9 : ℚ) =
      GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData.deg := by
    exact_mod_cast hparams.1.symm
  have h := girthEightSDPChecks_of_linkIdentification T hgeom
    GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData I hdeg
  simpa only [hparams.2, wEightReindexed] using h

end KazhdanHyp
end GroupApproximation
