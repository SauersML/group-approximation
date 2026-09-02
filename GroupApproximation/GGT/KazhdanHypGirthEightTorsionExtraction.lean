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
used by `PowerDiscCandidate` and the landed `CactusRelatorRetyping`; the
cancellation operation is supplied by `PowerDiscMirrorPairCut` and consumed
by `cancellationReducesArea_of_mirrorPairCut`; and the seam operation is
stated at the `CombMap` level with
`SeamGluing.ExposedPairing`, `Pairing.toPairing`, and its Euler-certified
spherical planar certificate.  Existing constructions
`nonempty_powerDiscCandidate_of_cactusRetyping`,
`leastPowerDisc_of_filling`,
`cancellationReducesArea_of_mirrorPairCut`,
`powerDiscSphereGluing_of_eulerCounts`, and
`triangularRelatorSphericalMap_of_powerDiscGluing` are consumed by name.

The source proof is complete once those cellular operations are proved.  The
model lemmas below test the contracts on the trivial-group, empty-cell,
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

/-- The remaining filling contract, now expressed through the landed
`CactusRelatorRetyping` construction.  A supplied cactus complement must
produce an exact repeated boundary; the imported constructor then turns it
into the candidate consumed by the least-area theorem. -/
def CactusPowerBoundaryFilling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator)),
      PresentedGroup.mk
          (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0}
          (triangleRelatorWords T),
        ∃ C : VanKampen.CactusRelatorRetyping Delta,
          C.diagram.boundaryWord =
            (List.replicate n (word.map signedFreeRelLetter)).flatten

/-- The remaining cancellation contract is the concrete mirror-pair output
`PowerDiscMirrorPairCut`.  The imported `cancellationReducesArea_of_mirrorPairCut`
theorem performs the area argument, so this module no longer asks callers to
re-prove its abstract `CancellationReducesArea` conclusion. -/
def MirrorPairCutSupply
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDiscCandidate T g n),
    ∀ (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T)),
    D.diagram.relatorCells = pre ++ C₁ :: (between ++ C₂ :: suf) →
    (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
      (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1 →
    PowerDiscMirrorPairCut D

/-- The remaining seam certificate uses the landed exposed-boundary pairing.
`ExposedPairing.toPairing` supplies the closed-map edge involution, and the
landed `powerDiscSphereGluing_of_eulerCounts` supplies sphericality from the
explicit Euler data and the already-planar disc.  Only the Euler, literal
corner, and no-mirror certificates remain. -/
def ExposedPairingEulerCertificate
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n) : Prop :=
  (∀ j, ¬ RelatorIsProperPower (TriangularHodgeLayer.relator (T j))) →
    ∃ B : VanKampen.SeamGluing.ExposedPairing D.diagram n,
      let S : VanKampen.SeamGluing.Pairing D.diagram n := B.toPairing
      VanKampen.SeamGluing.Pairing.EulerTwoCountData S ∧
        (∀ v, VertexCornerCertificate T
          (cornerCycleOfCombMap S.closedMap v)) ∧
        (∀ v, CellularReducedAt
          (VertexCornerCertificate T (cornerCycleOfCombMap S.closedMap v)))

/-- A residual-input package keeps the three still-missing constructions
aligned to the same triangular presentation. -/
structure ExtractionInputs
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) where
  /-- Exact repeated-boundary cactus retyping. -/
  filling : CactusPowerBoundaryFilling T
  /-- Concrete output for every cancelling mirror pair. -/
  mirrorCut : MirrorPairCutSupply T
  /-- Exposed seam pairing and its remaining local certificates. -/
  seam : ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n), ExposedPairingEulerCertificate T D

/-! ## The least-area disc and cyclic sphere -/

/-- The three cellular operations produce a labelled reduced spherical map for
every finite-order input whose defining relators are not proper powers.  The
least-area choice is made by `leastPowerDisc_of_filling`; its reduced field is
supplied by `cancellationReducesArea_of_mirrorPairCut`, and the cyclic seam is
converted by the landed `powerDiscSphereGluing_of_eulerCounts`. -/
theorem sphericalExtraction_of_combMapOperations
    (H : ExtractionInputs T) :
    ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
      0 < n → g ^ n = 1 → g ≠ 1 →
      (∀ j, ¬ RelatorIsProperPower
        (TriangularHodgeLayer.relator (T j))) →
      ∃ M : VanKampen.CombMap.{0},
        Nonempty (VanKampen.TriangularRelatorSphericalMap T M) := by
  intro g n hn hpow hne hnoProper
  let D : PowerDisc T g n := leastPowerDisc_of_filling hn hpow hne
    (fun _hn _hpow _hne ↦ by
      obtain ⟨word, hword⟩ := exists_signedWord_represents g
      obtain ⟨Delta, C, hboundary⟩ := H.filling g n hn hpow hne word hword
      exact nonempty_powerDiscCandidate_of_cactusRetyping word hword
        hn hpow hne Delta C hboundary)
    (fun candidate ↦
      cancellationReducesArea_of_mirrorPairCut candidate
        (H.mirrorCut g n candidate))
  have hD : PowerDisc T g n := D
  obtain ⟨B, hB⟩ := H.seam g n hD hnoProper
  dsimp at hB
  obtain ⟨hcounts, hcertificate, hcellular⟩ := hB
  have hglue : PowerDiscSphereGluing hD :=
    powerDiscSphereGluing_of_eulerCounts hD B.toPairing hcounts
      hD.diagram.planar hcertificate hcellular
  exact exists_labelledSphere_of_powerDiscGluing hD hglue

/-- The extraction theorem is exactly the input expected by
`presented_isPowerTorsionFree_of_sphericalExtraction`. -/
theorem presented_isPowerTorsionFree_of_combMapOperations
    {d : ℕ} (hchecks : GirthEightChecks T d)
    (H : ExtractionInputs T) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
  presented_isPowerTorsionFree_of_sphericalExtraction hchecks
    (sphericalExtraction_of_combMapOperations H)

/-! ## Model tests for the residual contracts -/

/-- The cactus filling contract holds for a trivial presented group because
the nonidentity branch is impossible. -/
theorem cactusPowerBoundaryFilling_trivialModel
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (htrivial : ∀ g : TriangularHodgeLayer.Presented T, g = 1) :
    CactusPowerBoundaryFilling T := by
  intro g n hn hpow hne word hword
  exact (hne (htrivial g)).elim

/-- The same contract is true in every power-torsion-free presented group;
this is the rank-one-free-group model after identifying its empty-relator
presentation with `FreeGroup (Fin 1)`. -/
theorem cactusPowerBoundaryFilling_freeGroupOneModel
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hfree : IsPowerTorsionFree (TriangularHodgeLayer.Presented T)) :
    CactusPowerBoundaryFilling T := by
  intro g n hn hpow hne word hword
  exact (hne (hfree g n hn hpow)).elim

/-- An everywhere empty relator-cell family is a model of the concrete
mirror-cut supply: the ordered mirror-pair premise is impossible. -/
theorem mirrorPairCutSupply_emptyModel
    (hempty : ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
      (D : PowerDiscCandidate T g n), D.diagram.relatorCells = []) :
    MirrorPairCutSupply T := by
  intro g n D pre between suf C₁ C₂ hsplit _hcancel
  rw [hempty g n D] at hsplit
  have hlength := congrArg List.length hsplit
  simp only [List.length_nil, List.length_append, List.length_cons] at hlength
  omega

/-- Supplying the seam certificate itself gives a nonvacuous model of the
`ExposedPairingEulerCertificate` contract.  The conclusion retains the
full exposed pairing and planar map data, so it is not a proposition about an
arbitrary empty map. -/
theorem exposedPairingEulerCertificate_model
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    (B : VanKampen.SeamGluing.ExposedPairing D.diagram n)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData B.toPairing)
    (certificate : ∀ v, VertexCornerCertificate T
      (cornerCycleOfCombMap B.toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt
      (VertexCornerCertificate T
        (cornerCycleOfCombMap B.toPairing.closedMap v))) :
    ExposedPairingEulerCertificate T D := by
  intro _hnoProper
  refine ⟨B, ?_⟩
  dsimp
  exact ⟨hcounts, certificate, hcellular⟩

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
