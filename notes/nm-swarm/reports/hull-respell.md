# hull-respell lane report

## Scope
The relator re-spelling of Hull's Theorem 7.1 at Osin's Theorem 2.4. The job is to remove the
family-form admission and the re-spelling input from the manuscript quotient field
`Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement`, so that it rests only on the two geometric
leaves.

Since 2026-09-13 (every-line swarm) this lane integrates the hgreendlinger wall. The target is
`theorem relativeGreendlingerQuasiGeodesicLeastArea_closed :
GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`.

## hgreendlinger: piece Props (decided 2026-09-13, landed a452fa727, probe 0913-012115-15640 GREEN)

The two modules below compiled green on base a452fa727, whose bytes equal origin/main.
`#audit_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Both are queued for root wiring.

`GGT/VanKampen/Estimating/OsinAppendixGreendlingerParts` holds four part Props. Each has the
quantifier prefix of `OsinLemma94SectionStatement`:
`∀ G D, hyperbolic → ∀ λ c μ, 0<λ≤1, 0≤c, 0<μ≤1/16 → ∃ ε₀, ∀ ε ≥ ε₀, ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀, ∀ W,
OsinCCondition D W ε μ λ c ρ → <input>`.

| Prop | input (`OsinAppendixSectionInduction`) | owner |
|---|---|---|
| `OsinMultipleEdgeCutSectionStatement` | `MultipleEdgeCutInput D λ c ε W` (G2) | hull-select |
| `OsinLoopCutSectionStatement` | `LoopCutInput D λ c ε W` (G2) | go-lemma42 |
| `OsinEulerCountSectionStatement` | `EulerCountInput D λ c ε W` (G3, G4) | hull-euler |
| `OsinDescentSectionStatement` | `DescentInput D λ c μ ε W` (G6) | dgo-analytic |

Assemblies:
- `osinSection97Inputs_of_parts hmulti hloop heuler hdescent : OsinSection97InputsStatement`. The
  thresholds combine by maxima.
- `osinLemma97Section_of_parts h94 hmulti hloop heuler hdescent : OsinLemma97SectionStatement`.
- `relativeGreendlingerQuasiGeodesicLeastArea_of_parts h94 hmulti hloop heuler hdescent :
  RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, with O52 discharged by `Embedded.o52LeastArea`.

`GGT/VanKampen/Estimating/OsinAppendixGreendlingerPocketParts` is the alternative route to the Euler
and descent parts, through `OsinAppendixLemma97Pocket` (42e5d2843). That module builds as a
dependency of this probe.

| Prop | input | owner |
|---|---|---|
| `OsinPhiPrimeCountSectionStatement` | `PhiPrimeCountInput D λ c ε W` (`OsinAppendixEulerCount`) | hull-euler |
| `OsinSectionPocketCutSectionStatement` | `SectionPocketCutInput D λ c ε W` (`OsinAppendixDescentCut`) | dgo-analytic |

The owners follow the 09-13 swap: hull-euler owns PhiPrimeCountInput and dgo-analytic owns
SectionPocketCutInput.

Assemblies:
- `osinEulerCountSection_of_phiPrimeCount hcount : OsinEulerCountSectionStatement`.
- `osinSection97PocketInputs_of_parts hmulti hloop hcount hpocket : OsinSection97PocketInputsStatement`.
- `osinDescentSection_of_pocketParts h94 hmulti hloop hcount hpocket : OsinDescentSectionStatement`.
- `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts h94 hmulti hloop hcount hpocket`.

A part proved at fixed parameters under `OsinCCondition` gives its section Prop with `ε₀ = 0` and
`ρ₀ = 1`.

### Residual Props for the closed target
- `OsinLemma94SectionStatement` (h94). hull-unbound replaced the RunInput route with
  `osinLemma94Section_of_pieces hmetric hrun` (`OsinLemma94Pieces.lean`, b8441172e):
  - `hmetric : OsinLemma94AntiparallelMetricStatement`. Main has the theorem
    `osinLemma94AntiparallelMetric` (`OsinLemma94AntiparallelMetric.lean:61`, hull-count94).
  - `hrun : OsinLemma94PlanarRunInput` is open (hull-unbound).
- One of these two sets:
  - `OsinMultipleEdgeCutSectionStatement`, `OsinLoopCutSectionStatement`,
    `OsinEulerCountSectionStatement`, `OsinDescentSectionStatement`;
  - `OsinMultipleEdgeCutSectionStatement`, `OsinLoopCutSectionStatement`,
    `OsinPhiPrimeCountSectionStatement`, `OsinSectionPocketCutSectionStatement`.

On origin/main (5f9c16b7b) no producer of any of the six fixed-parameter inputs exists yet. The flip
to `relativeGreendlingerQuasiGeodesicLeastArea_closed` happens when h94 and one of the two sets land.

## W1 helper: pocket shelling (item of 09-13 ~02:00)
The lead asked this lane for the shelling producer of the pocket cut core, that is
`FaceSetEarStatement` (`VanKampen/FaceSetPeelProducer.lean:171`), which closes only from
`FaceSetEarData` (`VanKampen/FaceSetEar.lean:57`).

- **The ear statements are false.** `GGT/VanKampen/FaceSetEarSpurCounterexample` (9dda53a05, probe
  0913-025312-66955 GREEN) proves `not_faceSetEarStatement : ¬ Embedded.FaceSetEarStatement.{0,0,0}`
  and `not_faceSetEarDataStatement : ¬ Embedded.FaceSetEarDataStatement.{0,0,0}`, both with
  `#audit_closed_axioms`.
  - The map has four darts, face cycles `[0,1,2]` and `[3]`, and a spur `{0,1}` inside the G-face
    `face 0`.
  - The face set `{face 0}` has the boundary cycle `[2]` and no peelable ear.
- Consumers with a binder on the false Prop: `FaceSetPeelProducer.lean:182,194`,
  `Estimating/PieceConstruction.lean:30,56` and `Estimating/PieceCore.lean:228`.
- The same map refutes `RegionShellingStatement` (`FaceShelling.lean:194`), because a `FaceShelling`
  step never erases a spur.
  - audit-sec5 holds that module (`VanKampen/RegionShellingSpurCounterexample.lean`, not yet on main),
    and this lane does not duplicate it.
  - Consumer with a binder: `Estimating/PieceConstruction.lean:83`.
- Correct form: face-set pasting must allow alpha-pair erasure (`FaceSetWordHomotopy.eraseAlphaPair`).
  `CellShellingWithGCells` carries it through `gMove`.
- **Superseded.** The lead's ruling of 09-13 ~03:35 drops the rebased `RegionCutData`. The carrier is
  an `IsDiscRegion` face set with `DiscDiagram.ofPlanar` on `replaceGRegion`.
  - No consumer then needs a shelling of the pocket, so this lane builds no producer.
  - It did not negotiate piece (a) with dgo-analytic, which is now on DescentInput and
    `OsinPocketOuterPart`.
- **Design on file**, in case a consumer of `RegionCutWithGCells.shelling` appears. Let
  `region : IsDiscRegion Δ outside` with `Δ.outerFace ∈ outside`, and let `fs` list the relator faces
  outside `outside`. The enclosed faces then admit
  `CellShellingWithGCells Δ (univ.filter (· ∉ outside)) gs (fs.map (orientedFaceDarts Δ · false))
  (invDarts Δ region.cycle)`. The proof:
  - `reclosedMap Δ outside region` is planar.
  - Induct by edge deletion as in `isRelatorProduct_of_planar`.
  - A relator face attaches by `step` and a G-face by `gMove {f}` along
    `FaceSetMoveSequence.shellStep`. A one-face tree closes by `gMove ∅` through alpha pairs.

## `HullSC.HullRelatorRespellingStatement` (roster: if a consumer remains after theoremc-retire)
- One consumer chain remains on main, in root-wired `Manuscript/NonMF/TheoremCAssembly.lean`:
  `hullRelatorRespelling` (`sorry`) feeds `hullLemma44FamilyInclusionJoint`, which feeds
  `hullLemma44FamilyInclusion` (`dgoProposition414Uniform hullLemma44FamilyInclusionJoint`).
- `hullLemma44FamilyInclusionJoint` also consumes the other three sorry declarations that
  theoremc-retire is told to delete. Retiring them means retiring this chain. This was reported to the lead.
- This lane does not prove the statement. `GGT/HullSCLemma44RespellingWitness` documents that it is too
  strong as printed, because `eps` and `rho` are chosen before `W`. The least-area route
  `GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves` does not use it.

## Compiled on main (probe 0911-211417-50221 GREEN, last landing 3832abdb7)
- C1, the un-coned joint image: `GGT.cyclicPeripheralRemovalStatement : CyclicPeripheralRemovalStatement`.
  It is closed (`#audit_closed_axioms`) and lives in GGT/HullSCUnconeThin. It builds over GGT/HullSCUncone{Expansion, ClosingJump,
  CosetAvoidance, TriangleConnectors, PathPoints, CosetCoordinates, LemmaA, Walk, LemmaB, Sides} and
  GGT/HullSCCyclicPeripheralRemoval.
- C2, bounded joint re-spelling at Hull's published relator:
  `HullSC.exists_publishedRelator_boundedJointRespelling`, in GGT/HullSCLemma44BoundedJointRespellingHullRelator.
- C3, Osin's Theorem 2.4 at the published relator from the bounded leaves:
  `GGT.RelHyp.osin24HullStep_of_boundedLeaves`, in GGT/RelHypOsin24PublishedHullStep. It is consumed by
  `fournierFacioQuotientStatement_of_hullStep` (GGT/RelHypProp23FromHullStep).
- The image form of Osin's Lemma 5.1 from the least-area certificate:
  `HullSC.boundedImageEmbeddingStatement_of_quasiGeodesicLeastArea`, in GGT/HullSCBoundedImageEmbeddingLeastArea.
- The quotient field over the least-area leaves, in GGT/RelHypProp23FromLeastAreaLeaves:
  ```lean
  theorem GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves
      (hgreendlinger :
        GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
      (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
      Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement
  ```
  It is consumed by `Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`
  (field `smallCancellationQuotient`).
- Census: `metadata/nm-census-rows/hull-respell.tsv`, rows LINE:1636, LINE:1644, LINE:1675, all `partial`. The
  status is partial because of the hgreendlinger and hbridge leaves.

## Open leaves
1. hgreendlinger: see the residual Props above.
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` (HullSCLemma51EmbeddedBridge) is Osin's
   Lemma 5.1 in embedded form. It is owned by hull-bridge and hull-component, via the letter pullback.

## Relaunch 2026-09-12
- The relaunch directive gave this lane "E1–E6" and `phiSubdividedGraph`. Those are the six
  GGT/VanKampen/Estimating/OsinAppendixEuler* modules, which belong to hull-euler. hull-respell edited none of them.
- There were no stranded edits: every hull-respell file in the shared tree matches origin/main.
- One batch probe of the six Euler modules ran under hull-euler's lane name (0912-092011-96837) and
  FAILED in OsinAppendixEulerSubdivided. The diagnosis went to hull-euler, and hull-euler later compiled all
  seven Euler modules (0912-104426-41122).

## Next
- The lead has been asked for the next item (09-13 ~04:00). Proposed: a piece of the weighted planar van
  Kampen lemma (`PlanarVanKampenWeighted`, kh-torsion, not on main yet).
- Flip to `relativeGreendlingerQuasiGeodesicLeastArea_closed` as h94 and the parts land. A watcher on
  landed.log follows the part owners.
