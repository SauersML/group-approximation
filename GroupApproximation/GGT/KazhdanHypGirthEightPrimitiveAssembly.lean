import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives2

/-!
# Assembly of the girth-eight van Kampen inputs

This file separates the constructions supplied by the van Kampen lane from
the five genuinely geometric inputs of the girth-eight interface.  The
cyclic-map orbit facts and the literal triangular face positions are imported
from `KazhdanHypGirthEightPrimitives`; the least-area and rotated-copy
constructions are the lemmas in `KazhdanHypGirthEightPrimitives2`.

The remaining record fields are local-data construction, centered-window
star geometry, cancellation surgery, literal power fillings, and seam
gluing.  They are all strictly smaller than the final
`GirthEightDiagramPrimitives` record, so a van Kampen implementation can fill
them one at a time.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightPrimitiveAssembly

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GirthEightPrimitives2

section

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## The residual construction contract -/

/-- The residual geometric data from which the full interface is assembled.
The first field gives cellular local data for each reduced disc.  The next
field is Papasoglu's centered-window star estimate.  The last three fields
are respectively the cancellation, filling, and seam inputs in
Huebschmann's power-disc argument. -/
structure ConstructionInputs where
  /-- Cellular relator coverage, reduced link walks, and boundary immersion. -/
  localData : ∀
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)),
    Delta.Reduced → TriangularDiagramLocalData T Delta
  /-- Disjoint star layers around a far point in a geodesic triangle. -/
  successiveStars : ∀ (delta : ℕ)
    (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q, Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q, Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    SuccessiveStarLayers T
  /-- A cancelling pair in a power-disc admits a strictly smaller filling. -/
  cancellation : ∀
    (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDiscCandidate T g n),
    CancellationReducesArea D
  /-- A literal power boundary has a relator-only van Kampen filling. -/
  filling : ∀
    (g : TriangularHodgeLayer.Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator)),
      PresentedGroup.mk
          (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta.boundaryWord =
          (List.replicate n (word.map signedFreeRelLetter)).flatten ∧
        RelatorOnly T Delta
  /-- Rotated-copy gluing gives the labelled reduced sphere. -/
  gluing : ∀
    (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n),
    (∀ j, ¬ RelatorIsProperPower
      (TriangularHodgeLayer.relator (T j))) →
    PowerDiscSphereGluing D

/-! ## The easy reduction and the exact constructor -/

/-- Local relator coverage gives the identity base-cell reduction.  This is
the `identityRelatorOnlyReduction` argument of
`VanKampen.CombMapReduction`, specialized to a triangular table. -/
def relatorOnlyReduction_of_localData
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (hred : Delta.Reduced) (L : TriangularDiagramLocalData T Delta) :
    RelatorOnlyReduction T Delta where
  diagram := Delta
  boundaryWord_eq := rfl
  rCellCount_le := Delta.rCellCount_le_innerFaceCount
  reduced := hred
  relatorOnly := { cell := L.innerFaceCell }

/-- Assemble every field of `GirthEightDiagramPrimitives` from the residual
construction contract.  The least-area theorem is
`leastPowerDisc_of_literalFilling`; its only nonformal input is the supplied
cancellation surgery.  The spherical field is
`gluePowerDisc_of_rotationGluing`. -/
noncomputable def ConstructionInputs.toPrimitives
    (H : ConstructionInputs T) : GirthEightDiagramPrimitives T where
  localProjection := LocalDiagramProjections.canonical
  cornerCycle := GirthEightPrimitives.cornerCycle
  facePositions := GirthEightPrimitives.facePositions
  removeBaseCells := fun Delta hred ↦
    relatorOnlyReduction_of_localData Delta hred (H.localData Delta hred)
  successiveStars := H.successiveStars
  leastPowerDisc := fun g n hn hpow hne ↦
    leastPowerDisc_of_literalFilling hn hpow hne
      (fun word hword _hn _hpow _hne ↦ H.filling g n hn hpow hne word hword)
      (fun D ↦ H.cancellation g n D)
  gluePowerDisc := fun g n D hnoProper ↦
    gluePowerDisc_of_rotationGluing D (fun _ ↦ H.gluing g n D hnoProper)
      hnoProper

end

/-! ## A nonvacuous model for the residual contract's local component -/

section Model

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- The one-triangle map has the local boundary-valence estimate used by the
repaired interface.  Its cyclic orbit is the model for the local-data field. -/
theorem oneTriangle_localProjection_model :
    ∀ d : VanKampen.OneTriangleDart,
      2 ≤ VanKampen.oneTriangleCombMap.vertexDegree
        (VanKampen.oneTriangleCombMap.vertexOf d) :=
  oneTriangle_vertexDegree_two_le

end Model

end GirthEightPrimitiveAssembly
end GGT
end GroupApproximation
