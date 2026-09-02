import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives2

/-!
# Huebschmann finite-order extraction for girth-eight triangle tables

Huebschmann, *Cohomology theory of aspherical groups and of small cancellation
groups*, Theorem 3, is quoted in Duda, *Torsion subgroups of small cancellation
groups*, arXiv:2112.01912, `all3.tex`, in the proof of Theorem A.  The printed
argument first takes a word `w` for a finite-order element, chooses a least-area
disc whose boundary is the power `w^n`, and uses the cyclic partition of that
boundary to glue `n` copies.  A mirror pair in the least disc would admit a
strictly smaller cancellation, so the glued sphere is reduced.  The girth-eight
link estimate then gives the triangular spherical curvature contradiction.

This file proves the extraction after the three genuinely cellular operations
are supplied.  The filling operation is stated with the literal signed word
used by `PowerDiscCandidate`; the cancellation operation is exactly the
`CancellationReducesArea` input of `leastPowerDisc_of_literalFilling`; and the
seam operation is stated at the `CombMap` level with
`SeamGluing.ExposedPairing`, `Pairing.toPairing`, and its spherical planar
certificate.  Existing constructions
`nonempty_powerDiscCandidate_of_literalFilling`,
`leastPowerDisc_of_literalFilling`,
`powerDiscSphereGluing_of_seam`, and
`triangularRelatorSphericalMap_of_powerDiscGluing` are consumed by name.

The source proof is complete once those cellular operations are proved.  The
model lemmas below test the contracts on the trivial-group, empty-word,
two-point, and rank-one-free-group boundary cases, so the contracts do not
silently rely on a nonempty boundary or on a nontrivial torsion input.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace GirthEightTorsionExtraction

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GirthEightPrimitives2

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## The three residual cellular operations -/

/-- A literal van Kampen filling for the exact repeated boundary used by
`PowerDiscCandidate`.  This is the filling step in Huebschmann's least-area
disc argument, with the representative word fixed before the disc is chosen.
The conclusion is strictly smaller than a spherical extraction: it contains
one planar disc and no cyclic gluing or spherical local data. -/
def LiteralPowerBoundaryFilling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator)),
      PresentedGroup.mk
          (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0}
          (triangleRelatorWords T),
        Delta.boundaryWord =
          (List.replicate n (word.map signedFreeRelLetter)).flatten ∧
        RelatorOnly T Delta

/-- The exact least-area cancellation operation needed by
`leastPowerDiscCandidate_reduced`: every cancelling ordered pair of stored
relator cells is removed by a same-boundary candidate of strictly smaller
relator area.  The output is deliberately the candidate expected by the
existing least-area theorem, so no unproved map surgery is hidden in this
contract. -/
def CombMapCancellationSurgery
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDiscCandidate T g n),
    CancellationReducesArea D

/-- The exact `CombMap` seam operation for cyclically gluing copies of a least
power disc.  `B` pairs exposed boundary darts, `B.toPairing` installs the
closed-map edge involution, and the supplied planar, corner-label, and
no-mirror fields are precisely what
`powerDiscSphereGluing_of_seam` consumes.  The no-proper-power hypothesis is
available at the seam stage because it is the branch in which mirror seams
are excluded. -/
def CombMapSphericalSeam
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n) : Prop :=
  (∀ j, ¬ RelatorIsProperPower (TriangularHodgeLayer.relator (T j))) →
    ∃ B : VanKampen.SeamGluing.ExposedPairing D.diagram n,
      let S : VanKampen.SeamGluing.Pairing D.diagram n := B.toPairing
      S.Spherical ∧
        (∀ v, VertexCornerCertificate T
          (cornerCycleOfCombMap S.closedMap v)) ∧
        (∀ v, CellularReducedAt
          (VertexCornerCertificate T (cornerCycleOfCombMap S.closedMap v)))

/-- A residual-input package keeps the filling, cancellation, and seam
operations aligned to the same triangular presentation. -/
structure ExtractionInputs
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) where
  /-- Literal repeated-boundary fillings. -/
  filling : LiteralPowerBoundaryFilling T
  /-- Strict area-decreasing cancellation surgery. -/
  cancellation : CombMapCancellationSurgery T
  /-- Spherical cyclic seam gluing for least power discs. -/
  seam : ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n), CombMapSphericalSeam T D

/-! ## Connecting the seam operation to the existing sphere certificate -/

/-- A `CombMapSphericalSeam` supplies the exact fields of the existing
`PowerDiscSphereGluing` record. -/
theorem powerDiscSphereGluing_of_combMapSphericalSeam
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    (hseam : CombMapSphericalSeam T D)
    (hnoProper : ∀ j, ¬ RelatorIsProperPower
      (TriangularHodgeLayer.relator (T j))) :
    PowerDiscSphereGluing D := by
  obtain ⟨B, hS, hcertificate, hcellular⟩ := hseam hnoProper
  exact powerDiscSphereGluing_of_seam D B.toPairing hS hcertificate hcellular

/-- Literal filling gives the nonempty candidate required by
`leastPowerDisc_of_literalFilling`. -/
/-! ## The least-area disc and cyclic sphere -/

/-- The three cellular operations produce a labelled reduced spherical map for
every finite-order input whose defining relators are not proper powers.  The
least-area choice is made by `leastPowerDisc_of_literalFilling`; its reduced
field is supplied by the cancellation surgery, and the cyclic seam is
converted by `powerDiscSphereGluing_of_combMapSphericalSeam`. -/
theorem sphericalExtraction_of_combMapOperations
    (H : ExtractionInputs T) :
    ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
      0 < n → g ^ n = 1 → g ≠ 1 →
      (∀ j, ¬ RelatorIsProperPower
        (TriangularHodgeLayer.relator (T j))) →
      ∃ M : VanKampen.CombMap.{0},
        Nonempty (VanKampen.TriangularRelatorSphericalMap T M) := by
  intro g n hn hpow hne hnoProper
  let D : PowerDisc T g n := leastPowerDisc_of_literalFilling hn hpow hne
    (fun word hword _hn _hpow _hne ↦ by
      exact H.filling g n hn hpow hne word hword)
    (fun candidate ↦ H.cancellation g n candidate)
  have hD : PowerDisc T g n := D
  have hseam : CombMapSphericalSeam T hD := H.seam g n hD
  have hglue : PowerDiscSphereGluing hD :=
    powerDiscSphereGluing_of_combMapSphericalSeam hD hseam hnoProper
  exact exists_labelledSphere_of_powerDiscGluing hD hglue

/-- The extraction theorem is exactly the input expected by
`presented_isPowerTorsionFree_of_sphericalExtraction`. -/
theorem presented_isPowerTorsionFree_of_combMapOperations
    {d : ℕ} (hchecks : GirthEightChecks T d)
    (H : ExtractionInputs T) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
  presented_isPowerTorsionFree_of_sphericalExtraction hchecks
    H.sphericalExtraction_of_combMapOperations

/-! ## Model tests for the residual contracts -/

/-- The literal filling contract holds for a trivial presented group because
the nonidentity branch is impossible. -/
theorem literalPowerBoundaryFilling_trivialModel
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (htrivial : ∀ g : TriangularHodgeLayer.Presented T, g = 1) :
    LiteralPowerBoundaryFilling T := by
  intro g n hn hpow hne word hword
  exact (hne (htrivial g)).elim

/-- The same contract is true in every power-torsion-free presented group;
this is the rank-one-free-group model after identifying its empty-relator
presentation with `FreeGroup (Fin 1)`. -/
theorem literalPowerBoundaryFilling_freeGroupOneModel
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hfree : IsPowerTorsionFree (TriangularHodgeLayer.Presented T)) :
    LiteralPowerBoundaryFilling T := by
  intro g n hn hpow hne word hword
  exact (hne (hfree g n hn hpow)).elim

/-- An empty relator-cell list is the zero-area empty-word model of the
cancellation contract.  The imported theorem is the exact minimality proof
used by the least-area construction. -/
theorem combMapCancellationSurgery_emptyWordModel
    (D : PowerDiscCandidate T g n) (hword : D.word = [])
    (hcells : D.diagram.relatorCells = []) :
    CancellationReducesArea D := by
  exact cancellationReducesArea_of_noCells D hcells

/-- Supplying the seam certificate itself gives a nonvacuous model of the
`CombMapSphericalSeam` contract.  The conclusion retains the full exposed
pairing and planar map data, so it is not a proposition about an arbitrary
empty map. -/
theorem combMapSphericalSeam_certificateModel
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    (B : VanKampen.SeamGluing.ExposedPairing D.diagram n)
    (hS : B.toPairing.Spherical)
    (certificate : ∀ v, VertexCornerCertificate T
      (cornerCycleOfCombMap B.toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt
      (VertexCornerCertificate T
        (cornerCycleOfCombMap B.toPairing.closedMap v))) :
    CombMapSphericalSeam T D := by
  intro hnoProper
  exact ⟨B, hS, certificate, hcellular⟩

/-- The two-point torsion model refutes localization at an empty obstruction
family, so the no-proper-power branch in the extraction theorem cannot be
discarded as a vacuous torsion statement. -/
theorem twoPoint_emptyObstruction_model :
    ¬ FiniteOrderForces (Multiplicative (ZMod 2)) PEmpty (fun _ ↦ False) :=
  not_finiteOrderForces_twoGroup_empty

end Table

end GirthEightTorsionExtraction
end GGT
end GroupApproximation
