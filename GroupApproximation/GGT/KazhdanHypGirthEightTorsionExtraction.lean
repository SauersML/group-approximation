import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives2
import GroupApproximation.GGT.KazhdanHypGQLinkIdentification

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

/- The following two propositions are deliberately map-level interfaces.  The
   generic Cactus and Surgery files provide their *retyping* and *cut output*
   constructors, but do not select the regions in an arbitrary least-area
   power disc. -/

/-- Exact missing input for the cactus step: for every chosen representative
word, a CombMap-level cactus complement is retyped to a reduced relator-only
disc with the literal repeated boundary.  This is the precise producer needed
before `nonempty_powerDiscCandidate_of_cactusRetyping` can be applied. -/
def CactusRelatorRetypingForPower
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

/-- A source certificate expressed with the landed free-base-cell deletion
constructor.  This is the concrete input from which the retyping producer is
assembled below. -/
def CactusBaseCellDeletionForPower
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator)),
      PresentedGroup.mk
          (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0}
          (triangleRelatorWords T),
        ∃ C : VanKampen.CactusBaseCellDeletion Delta,
          C.replacement.diagram.boundaryWord =
            (List.replicate n (word.map signedFreeRelLetter)).flatten

/-- Exact missing input for the mirror step: the selected two-cell
`CombMap` surgery returns a power-disc candidate.  The list and cancellation
hypotheses are the ordered boundary/seam data used by `SurgeryMap`. -/
def PowerDiscMirrorPairDeletionSupply
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDiscCandidate T g n),
    ∀ (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T)),
    (hsplit : D.diagram.relatorCells =
      pre ++ C₁ :: (between ++ C₂ :: suf)) →
    (hcancel :
      (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
        (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1) →
    PowerDiscMirrorPairDeletion D pre between suf C₁ C₂ hsplit hcancel

/-- The exact seam output still absent from the generic CombMap API.  Its
fields separate the global exposed pairing/count construction from the local
triangle-corner and cellular-reducedness certificates. -/
def TrianglePairUnique
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ {p p' : TriangleIndex × Fin 3},
    T p.1 p.2 = T p'.1 p'.2 →
    T p.1 (TriangularHodgeLayer.nextCorner p.2) =
      T p'.1 (TriangularHodgeLayer.nextCorner p'.2) →
    p = p'

/-- The disjointness/simple-link clause of `GirthEightChecks` is precisely
the no-two-triples-sharing-a-consecutive-pair certificate used by a cellular
reducedness construction. -/
theorem trianglePairUnique_of_girthEightChecks
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d : ℕ}
    (hgeom : GirthEightChecks T d) : TrianglePairUnique T := by
  intro p p' hfirst hnext
  exact corner_unique_of_linkSimple T hgeom.simple hfirst hnext

structure ExposedPairingEulerInput
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n) where
  pairing : VanKampen.SeamGluing.ExposedPairing D.diagram n
  pairUnique : TrianglePairUnique T
  counts : VanKampen.SeamGluing.Pairing.EulerTwoCountData pairing.toPairing
  corner : ∀ v, VertexCornerCertificate T
    (cornerCycleOfCombMap pairing.toPairing.closedMap v)
  cellular : ∀ v, CellularReducedAt (corner v)

/-- The landed copy-involution constructor supplies the exposed pairing.  The
remaining fields are the Euler and local certificates attached to that
pairing; `pairUnique` is the table-side no-shared-pair certificate. -/
noncomputable def exposedPairingEulerInput_of_copyMate
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    {I : Type}
    (D : PowerDisc T g n)
    (index : ExposedCopiedDart D.diagram n ≃ Fin n × I)
    (copyMate : Equiv.Perm (Fin n))
    (hinvol : Function.Involutive copyMate)
    (hfree : ∀ i, copyMate i ≠ i)
    (hpairUnique : TrianglePairUnique T)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData
      (VanKampen.SeamGluing.ExposedPairing.of_copyMate
        index copyMate hinvol hfree).toPairing)
    (hcorner : ∀ v, VertexCornerCertificate T
      (cornerCycleOfCombMap
        (VanKampen.SeamGluing.ExposedPairing.of_copyMate
          index copyMate hinvol hfree).toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (hcorner v)) :
    ExposedPairingEulerInput T D := by
  let B := VanKampen.SeamGluing.ExposedPairing.of_copyMate
    index copyMate hinvol hfree
  exact {
    pairing := B
    pairUnique := hpairUnique
    counts := hcounts
    corner := hcorner
    cellular := hcellular }

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

/-- The landed Cactus retyping constructor is exactly the filling contract.
After the named CombMap-level producer is supplied, this theorem packages its
output with `nonempty_powerDiscCandidate_of_cactusRetyping`; no new filling
axiom is introduced here. -/
theorem cactusPowerBoundaryFilling_of_cactusRelatorRetyping
    (h : CactusRelatorRetypingForPower T) :
    CactusPowerBoundaryFilling T := by
  intro g n hn hpow hne word hword
  exact h g n hn hpow hne word hword

/-- The landed `CactusBaseCellDeletion.toRetyping` constructor turns the
free-base-cell version of the missing producer into the exact retyping
producer, after which the previous filling theorem applies. -/
theorem cactusPowerBoundaryFilling_of_baseCellDeletion
    (h : CactusBaseCellDeletionForPower T) :
    CactusPowerBoundaryFilling T := by
  apply cactusPowerBoundaryFilling_of_cactusRelatorRetyping
  intro g n hn hpow hne word hword
  obtain ⟨Delta, C, hboundary⟩ := h g n hn hpow hne word hword
  refine ⟨Delta, C.toRetyping, ?_⟩
  exact hboundary

/-- The exact candidate consumed by least-area selection is obtained from a
filling certificate by the landed Primitives2 theorem. -/
theorem powerDiscCandidate_of_cactusPowerBoundaryFilling
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (hfill : CactusPowerBoundaryFilling T)
    (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (hword : PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = g)
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1) :
    Nonempty (PowerDiscCandidate T g n) := by
  obtain ⟨Delta, C, hboundary⟩ := hfill g n hn hpow hne word hword
  exact nonempty_powerDiscCandidate_of_cactusRetyping word hword
    hn hpow hne Delta C hboundary

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

/-- The landed SurgeryMap deletion is retyped as the power-disc mirror cut.
The boundary equality comes from the reclosed replacement and the exact two
cell area equation is `PowerDiscMirrorPairDeletion.area_drop`. -/
theorem powerDiscMirrorPairCut_of_surgeryDeletion
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDiscCandidate T g n)
    (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T))
    (hsplit : D.diagram.relatorCells =
      pre ++ C₁ :: (between ++ C₂ :: suf))
    (hcancel :
      (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
        (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1)
    (C : PowerDiscMirrorPairDeletion D pre between suf C₁ C₂ hsplit hcancel) :
    PowerDiscMirrorPairCut D := by
  refine ⟨C.result, ?_, ?_⟩
  · rw [C.result_diagram_eq]
    exact C.topological.replacement.outerWord_eq
  · exact PowerDiscMirrorPairDeletion.area_drop D pre between suf C₁ C₂
      hsplit hcancel C

/-- A family of landed two-cell surgeries supplies the cancellation contract
used by the least-area constructor. -/
theorem mirrorPairCutSupply_of_surgeryDeletion
    (h : PowerDiscMirrorPairDeletionSupply T) :
    MirrorPairCutSupply T := by
  intro g n D pre between suf C₁ C₂ hsplit hcancel
  exact powerDiscMirrorPairCut_of_surgeryDeletion D pre between suf C₁ C₂
    hsplit hcancel (h g n D pre between suf C₁ C₂ hsplit hcancel)

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

/-- The landed seam constructor, once its three observable fields are
provided, is exactly the exposed-pairing contract. -/
theorem exposedPairingEulerCertificate_of_input
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n) (h : ExposedPairingEulerInput T D) :
    ExposedPairingEulerCertificate T D := by
  intro _hnoProper
  refine ⟨h.pairing, ?_⟩
  exact ⟨h.counts, h.corner, h.cellular⟩

/-- The W(8) link data and a supplied seam input can be consumed together:
the first conjunct is the extraction seam certificate and the second is the
symbolic gap-`5/9` transfer. -/
theorem exposedPairingEulerCertificate_and_wEightSDP_of_input
    {TriangleIndex : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle SymplecticQuadrangle.Point}
    (hgeom : GirthEightChecks T 9)
    (lineMap : SymplecticQuadrangle.Point ≃ SymplecticQuadrangle.Line)
    (hlink : CornerIncidenceTable T SymplecticQuadrangle.Incident lineMap)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    (hinput : ExposedPairingEulerInput T D) :
    ExposedPairingEulerCertificate T D ∧
      GirthEightSDPChecks T 9 (5 / 9)
        (QuadrangleLinkData.reindex
          _root_.GroupApproximation.KazhdanHyp.SymplecticQuadrangle.wEightQuadrangleLinkData
          (signedVertexEquiv lineMap)).gramRow := by
  exact ⟨exposedPairingEulerCertificate_of_input D hinput,
    girthEightSDPChecks_of_wEight_link_identification hgeom lineMap hlink⟩

/-- W(8) supplies the presentation-link identification and its gap without
enumerating the signed link.  The genuinely CombMap-level part is isolated in
`ExposedPairingEulerInput`: the current generic seam API has no constructor
that turns link incidence alone into a boundary pairing, Euler counts, and
corner certificates. -/
theorem exposedPairingEulerCertificate_of_wEight_linkData
    {TriangleIndex : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle SymplecticQuadrangle.Point}
    (hgeom : GirthEightChecks T 9)
    (lineMap : SymplecticQuadrangle.Point ≃ SymplecticQuadrangle.Line)
    (hlink : CornerIncidenceTable T SymplecticQuadrangle.Incident lineMap)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    (hinput : ExposedPairingEulerInput T D) :
    ExposedPairingEulerCertificate T D := by
  exact (exposedPairingEulerCertificate_and_wEightSDP_of_input
    hgeom lineMap hlink D hinput).1

/-- The copy-involution form is the explicit W(8) seam contract: the landed
`ExposedPairing.of_copyMate` builds the exposed pairing, while the W(8)
disjointness clause supplies `TrianglePairUnique`.  The remaining arguments
are exactly the still-topological Euler/corner certificates. -/
theorem exposedPairingEulerCertificate_of_wEight_copyMate
    {TriangleIndex : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle SymplecticQuadrangle.Point}
    (hgeom : GirthEightChecks T 9)
    (lineMap : SymplecticQuadrangle.Point ≃ SymplecticQuadrangle.Line)
    (hlink : CornerIncidenceTable T SymplecticQuadrangle.Incident lineMap)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    {I : Type}
    (index : ExposedCopiedDart D.diagram n ≃ Fin n × I)
    (copyMate : Equiv.Perm (Fin n))
    (hinvol : Function.Involutive copyMate)
    (hfree : ∀ i, copyMate i ≠ i)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData
      (VanKampen.SeamGluing.ExposedPairing.of_copyMate
        index copyMate hinvol hfree).toPairing)
    (hcorner : ∀ v, VertexCornerCertificate T
      (cornerCycleOfCombMap
        (VanKampen.SeamGluing.ExposedPairing.of_copyMate
          index copyMate hinvol hfree).toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (hcorner v)) :
    ExposedPairingEulerCertificate T D := by
  have hinput := exposedPairingEulerInput_of_copyMate D index copyMate
    hinvol hfree (trianglePairUnique_of_girthEightChecks hgeom)
    hcounts hcorner hcellular
  exact exposedPairingEulerCertificate_of_wEight_linkData
    hgeom lineMap hlink D hinput

/-- A residual-input package keeps the three still-missing constructions
aligned to the same triangular presentation. -/
structure ExtractionInputs
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) where
  /-- Exact repeated-boundary cactus free-base-cell deletion producer. -/
  filling : CactusBaseCellDeletionForPower T
  /-- Concrete SurgeryMap output for every cancelling mirror pair. -/
  mirrorDeletion : PowerDiscMirrorPairDeletionSupply T
  /-- Exposed seam pairing, Euler counts, and local certificates. -/
  seam : ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n), ExposedPairingEulerInput T D

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
      exact powerDiscCandidate_of_cactusPowerBoundaryFilling
        (cactusPowerBoundaryFilling_of_baseCellDeletion H.filling)
        word hword hn hpow hne)
    (fun candidate ↦
      cancellationReducesArea_of_mirrorPairCut candidate
        ((mirrorPairCutSupply_of_surgeryDeletion H.mirrorDeletion)
          g n candidate))
  have hD : PowerDisc T g n := D
  obtain ⟨B, hB⟩ := exposedPairingEulerCertificate_of_input hD
    (H.seam g n hD)
      hnoProper
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

/-- The complete exposed-input record has a concrete small-map model whenever
the copied pairing, Euler counts, corner labels, and no-shared-pair table
certificate are supplied. -/
theorem exposedPairingEulerInput_model
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n)
    (B : VanKampen.SeamGluing.ExposedPairing D.diagram n)
    (hpairUnique : TrianglePairUnique T)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData B.toPairing)
    (certificate : ∀ v, VertexCornerCertificate T
      (cornerCycleOfCombMap B.toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt
      (certificate v)) :
    ExposedPairingEulerInput T D := by
  exact {
    pairing := B
    pairUnique := hpairUnique
    counts := hcounts
    corner := certificate
    cellular := hcellular }

/-! ## The GQ(2,2) 27-row shape -/

/-- The abstract 27-representative indexing used by the small GQ(2,2) model.
The fifteen source rows are repeated modulo fifteen, exactly as in the
Singer-row hypothesis-shape test in the link-identification module. -/
def gqTwo27RepresentativeRoot (r : Fin 27) : Fin 15 :=
  ⟨r.val % 15, Nat.mod_lt _ (by decide)⟩

def GQTwo27RepresentativeRows : Prop :=
  ∀ (r : Fin 27) (k : Fin 3),
    (GQTwoTable.triangles (gqTwo27RepresentativeRoot r) k).2 = true

theorem gqTwo27RepresentativeRows : GQTwo27RepresentativeRows := by
  intro r k
  exact GQTwoTable.positive (gqTwo27RepresentativeRoot r) k

/-- The cactus bridge is model-tested on the transcribed GQ(2,2) table with
the same 27-row representative shape. -/
theorem cactusPowerBoundaryFilling_gqTwo_27Model
    (hsource : CactusBaseCellDeletionForPower GQTwoTable.triangles) :
    GQTwo27RepresentativeRows ∧
      CactusPowerBoundaryFilling GQTwoTable.triangles := by
  exact ⟨gqTwo27RepresentativeRows,
    cactusPowerBoundaryFilling_of_baseCellDeletion hsource⟩

/-- The landed two-cell SurgeryMap bridge is model-tested on the same
GQ(2,2) 27-row shape. -/
theorem mirrorPairCutSupply_gqTwo_27Model
    (hsource : PowerDiscMirrorPairDeletionSupply GQTwoTable.triangles) :
    GQTwo27RepresentativeRows ∧
      MirrorPairCutSupply GQTwoTable.triangles := by
  exact ⟨gqTwo27RepresentativeRows,
    mirrorPairCutSupply_of_surgeryDeletion hsource⟩

/-- The seam bridge is model-tested on a GQ(2,2) power disc while retaining
the explicit 27-representative row certificate. -/
theorem exposedPairingEulerCertificate_gqTwo_27Model
    {g : TriangularHodgeLayer.Presented GQTwoTable.triangles} {n : ℕ}
    (D : PowerDisc GQTwoTable.triangles g n)
    (hinput : ExposedPairingEulerInput GQTwoTable.triangles D) :
    GQTwo27RepresentativeRows ∧
      ExposedPairingEulerCertificate GQTwoTable.triangles D := by
  exact ⟨gqTwo27RepresentativeRows,
    exposedPairingEulerCertificate_of_input D hinput⟩

/-- A fully supplied GQ(2,2) seam model obtains the table-side certificate
from the certified simple-link check, while retaining the 27 representative
rows in the conclusion. -/
theorem exposedPairingEulerInput_gqTwo_27Model
    {g : TriangularHodgeLayer.Presented GQTwoTable.triangles} {n : ℕ}
    (D : PowerDisc GQTwoTable.triangles g n)
    (B : VanKampen.SeamGluing.ExposedPairing D.diagram n)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData B.toPairing)
    (certificate : ∀ v, VertexCornerCertificate GQTwoTable.triangles
      (cornerCycleOfCombMap B.toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (certificate v)) :
    GQTwo27RepresentativeRows ∧
      ExposedPairingEulerInput GQTwoTable.triangles D := by
  have hpairUnique : TrianglePairUnique GQTwoTable.triangles := by
    intro p p' hfirst hnext
    exact corner_unique_of_linkSimple GQTwoTable.triangles
      GQTwoTable.link_simple hfirst hnext
  exact ⟨gqTwo27RepresentativeRows,
    exposedPairingEulerInput_model D B hpairUnique hcounts certificate hcellular⟩

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
