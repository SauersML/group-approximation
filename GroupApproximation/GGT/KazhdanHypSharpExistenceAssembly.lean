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

The torsion chain is source-audited as follows.  At the leaf,
`GroupApproximation.IsPowerTorsionFree G` is exactly

```
∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1.
```

For a checked table, `presented_isPowerTorsionFree_of_sphericalExtraction`
consumes `hchecks : GirthEightChecks T d` and an extractor with the exact
quantifiers

```
∀ (g : Presented T) (n : ℕ), 0 < n → g ^ n = 1 → g ≠ 1 →
  (∀ j, ¬ RelatorIsProperPower (relator (T j))) →
  ∃ M, Nonempty (TriangularRelatorSphericalMap T M).
```

It first applies `finiteOrderForcesRelatorProperPower_of_sphericalExtraction`
to the same `g`, positive `n`, and nonidentity premise.  The latter assumes
the no-proper-power branch, calls the extractor, and applies
`TriangularRelatorSphericalMap.false_of_girthEightChecks`.  The resulting
`FiniteOrderForcesRelatorProperPower T` is passed to
`presented_isPowerTorsionFree_of_finiteOrderForcesRelatorProperPower`; its
second input is `hchecks.relators_not_properPower`.

The latter input uses `positive_triangle_cube_of_relatorIsProperPower` and
`hchecks.noCube`; `hchecks.noCube` is obtained from the link-simplicity clause,
so a literal `(x,x,x)` relator is rejected exactly at the proper-power step.
The verifier's separate `noCubeCheck` is not needed by the current
`checkTable_true_girth` soundness theorem because the same fact follows from
the checked simplicity clause.

The extractor is
`sphericalExtraction_of_combMapOperations H`.  Given arbitrary `g` and
positive `n`, it first chooses an arbitrary-length signed word with
`exists_signedWord_represents`.  `H.filling` is consumed by
`cactusPowerBoundaryFilling_of_baseCellDeletion`, which gives a
`PowerDiscCandidate` whose `DiscDiagram` boundary is the literal repetition
of that whole word.  `leastPowerDisc_of_filling` then selects a least-area
candidate, and `H.mirrorDeletion` is consumed by
`mirrorPairCutSupply_of_surgeryDeletion` and
`cancellationReducesArea_of_mirrorPairCut` to supply its reducedness.
`H.seam` supplies `ExposedPairingEulerInput` for that same arbitrary `n`;
`powerDiscSphereGluing_of_eulerCounts` and
`exists_labelledSphere_of_powerDiscGluing` produce the labelled spherical map.
Thus the current formal extractor covers every positive exponent, not only
generator words or a fixed exponent.  The source theorem is stated for order
`1 < s < ∞`; the formal positive-exponent statement is stronger in its
quantifier, and the `n = 1` case is vacuous under `g ≠ 1` and `g ^ n = 1`.

The source audit also fixes the diagram-type boundary: the formal input is
always `PowerDisc.diagram : DiscDiagram`, constructed from a null-homotopy of
the boundary word `w^n`.  The cyclic gluing is a sphere from copies of that
disc.  The repository has no `AnnularDiagram` in this chain, so annular
diagrams from conjugacy or periodic-annulus arguments are not silently being
used as discs.  If the cactus producer cannot supply this actual disc, the
failure is at `CactusBaseCellDeletionForPower`, not in the Euler calculation.
The Euler fields explicitly require the disc's planar map and the seam's
connectedness/count data; no annulus is admitted by their types.

The available readiness theorem below proves infiniteness from the already
obtained torsion-free conclusion and positivity, and proves finite
presentation directly from finite generator and triangle types.  `GirthEightChecks`
alone does not currently imply infiniteness in the repository: the only
available infiniteness route is positivity plus torsion-freeness, while the
asphericity/universal-cover Euler-characteristic route from Huebschmann is not
formalized.  The exact missing implication is recorded in `REPORT.md`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace KazhdanHypSharpExistenceAssembly

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GirthEightPrimitives2
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

/-- The one generic CombMap operation not yet exported by the seam files.

The output is deliberately stated in the raw copy-mate form consumed by the
landed `ExposedPairing.of_copyMate` constructor.  In particular, this is
strictly smaller than `ExposedPairingEulerProducer`: it does not assert the
table-side `TrianglePairUnique` field.  The latter is supplied by the W(8)
`GirthEightChecks` disjointness clause below.  A sep2fix implementation of
this proposition can therefore be consumed without changing any of the
W(8)-specific code in this module. -/
abbrev PlanarDiscExposedPairingEulerData : Prop :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n),
    ∃ (I : Type)
      (index : VanKampen.SeamGluing.ExposedCopiedDart D.diagram n ≃
        Fin n × I)
      (index_copy : ∀ d, (index d).1 = d.1.1)
      (copyMate : Equiv.Perm (Fin n))
      (hinvol : Function.Involutive copyMate)
      (hfree : ∀ i, copyMate i ≠ i),
      ∃ hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData
          (exposedPairing_of_copyMate D index index_copy copyMate hinvol hfree).toPairing,
        ∃ hcorner : ∀ v, VertexCornerCertificate T
          (cornerCycleOfCombMap
            (exposedPairing_of_copyMate D index index_copy copyMate hinvol hfree).toPairing.closedMap v),
          ∀ v, CellularReducedAt (hcorner v)

/-- A generic planar-disc seam package becomes the exposed-pairing producer
once the table-side pair-uniqueness certificate is supplied.  The pairing is
constructed by the landed `ExposedPairing.of_copyMate` API, and all three
local fields are passed through the landed `exposedPairingEulerInput_of_copyMate`
adapter. -/
theorem exposedPairingEulerProducer_of_planarDisc
    (hdata : PlanarDiscExposedPairingEulerData)
    (pairUnique : ∀ (Generator TriangleIndex : Type)
      (_ : Fintype Generator) (_ : DecidableEq Generator)
      (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
      TrianglePairUnique T) :
    ExposedPairingEulerProducer := by
  intro Generator TriangleIndex fg dg ft dt T g n D
  obtain ⟨I, index, index_copy, copyMate, hinvol, hfree,
    hcounts, hcorner, hcellular⟩ :=
    hdata Generator TriangleIndex fg dg ft dt T g n D
  exact exposedPairingEulerInput_of_copyMate D index index_copy copyMate
    hinvol hfree (pairUnique Generator TriangleIndex fg dg ft dt T)
    hcounts hcorner hcellular

/-- W(8)'s actual remainder of the preceding generic seam operation.  The
`GirthEightChecks` simple-link clause supplies `TrianglePairUnique`; the
corner-incidence data is consumed by
`exposedPairingEulerCertificate_of_wEight_linkData`.  Thus no table-wide
enumeration or second cellular argument is introduced here. -/
theorem wEightExposedPairingEulerProducer_of_planarDisc
    (hdata : PlanarDiscExposedPairingEulerData)
    {TriangleIndex : Type}
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex →
      TriangularHodgeLayer.Triangle SymplecticQuadrangle.Point}
    (hgeom : GirthEightChecks T 9)
    (lineMap : SymplecticQuadrangle.Point ≃ SymplecticQuadrangle.Line)
    (hlink : CornerIncidenceTable T SymplecticQuadrangle.Incident lineMap) :
    ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
      (D : PowerDisc T g n), ExposedPairingEulerInput T D := by
  intro g n D
  obtain ⟨I, index, index_copy, copyMate, hinvol, hfree,
    hcounts, hcorner, hcellular⟩ :=
    hdata SymplecticQuadrangle.Point TriangleIndex inferInstance inferInstance
      inferInstance inferInstance T g n D
  let hinput : ExposedPairingEulerInput T D :=
    exposedPairingEulerInput_of_copyMate D index index_copy copyMate hinvol hfree
      (trianglePairUnique_of_girthEightChecks hgeom) hcounts hcorner hcellular
  have _hcertificate := exposedPairingEulerCertificate_of_wEight_linkData
    hgeom lineMap hlink D hinput
  exact hinput

/-- The same generic seam data also reaches the landed spherical-map adapter.
This is the concrete use of `ExposedPairing.spherical_of_planarDisc`: the
adapter packages the Euler-two conclusion, source planarity, and the W(8)
corner/cellular certificates into the labelled spherical map consumed by the
Huebschmann extraction. -/
theorem labelledSphere_of_planarDiscSeamData
    (hdata : PlanarDiscExposedPairingEulerData)
    {Generator TriangleIndex : Type}
    [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (D : PowerDisc T g n) :
    ∃ M : VanKampen.CombMap.{0},
      Nonempty (VanKampen.TriangularRelatorSphericalMap T M) := by
  obtain ⟨I, index, index_copy, copyMate, hinvol, hfree,
    hcounts, hcorner, hcellular⟩ :=
    hdata Generator TriangleIndex inferInstance inferInstance
      inferInstance inferInstance T g n D
  let B := exposedPairing_of_copyMate D index index_copy copyMate hinvol hfree
  let G := powerDiscSphereGluing_of_planarDisc D B hcounts D.diagram.planar
    hcorner hcellular
  exact exists_labelledSphere_of_powerDiscGluing D G

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

/-! ## Readiness facts for the non-spectral conjuncts -/

/-- Positivity and the torsion-free conclusion make every checked triangular
presentation infinite.  This is the `C₃` quotient argument used by
`infinite_of_positive_of_torsionFree`; the finite-order localization is kept
as an explicit input because `GirthEightChecks` alone does not formalize
asphericity. -/
theorem infinite_of_girthEightChecks_and_torsionFree
    {Generator TriangleIndex : Type}
    [Fintype Generator] [DecidableEq Generator] [Nonempty Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (htf : IsPowerTorsionFree (TriangularHodgeLayer.Presented T)) :
    Infinite (TriangularHodgeLayer.Presented T) :=
  infinite_of_positive_of_torsionFree T hchecks.1 htf

/-- A finite triangular table presents a finitely presented group.  The
`GirthEightChecks` argument records the intended checked-table use; finite
presentation itself is supplied by the finite generator and triangle types. -/
theorem isFinitelyPresented_of_girthEightChecks
    {Generator TriangleIndex : Type}
    [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d : ℕ}
    (_hchecks : GirthEightChecks T d) :
    Group.IsFinitelyPresented (TriangularHodgeLayer.Presented T) :=
  inferInstance

/-- The two readiness conjuncts needed before torsion-freeness and
hyperbolicity are inserted into `SharpExistence`. -/
theorem infinite_and_finitelyPresented_of_girthEightChecks
    {Generator TriangleIndex : Type}
    [Fintype Generator] [DecidableEq Generator] [Nonempty Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (htf : IsPowerTorsionFree (TriangularHodgeLayer.Presented T)) :
    Infinite (TriangularHodgeLayer.Presented T) ∧
      Group.IsFinitelyPresented (TriangularHodgeLayer.Presented T) :=
  ⟨infinite_of_girthEightChecks_and_torsionFree hchecks htf,
    isFinitelyPresented_of_girthEightChecks hchecks⟩

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
  have htf : IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
    (girthEightTorsionFree_of_extractionProducers cactus mirror seam)
      _ _ inferInstance inferInstance inferInstance inferInstance inferInstance T 9 hgeom
  have hready := infinite_and_finitelyPresented_of_girthEightChecks hgeom htf
  have hhyp : Hyperbolic.IsHyperbolicGroup
      (TriangularHodgeLayer.Presented T) :=
    (girthEightHyperbolicity_of_diagramPrimitives diagramPrimitives)
      _ _ inferInstance inferInstance inferInstance inferInstance inferInstance
      T 9 hgeom
  exact ⟨TriangularHodgeLayer.Presented T, inferInstance,
    hready.1, hready.2, htf, hhyp,
    hasKazhdanPropertyT_of_girthEightSDPChecks hgeom hsdp⟩

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
  have hready := infinite_and_finitelyPresented_of_girthEightChecks
    GQTwoTable.girthEightChecks htf
  exact ⟨hready.1, hready.2, htf, hhyp⟩

end KazhdanHypSharpExistenceAssembly
end GGT
end GroupApproximation
