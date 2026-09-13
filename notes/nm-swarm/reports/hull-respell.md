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
- `OsinLemma94SectionStatement` (h94). hull-unbound's second split
  `osinLemma94Section_of_planarPieces hmetric hreal hcount hone htwo`
  (`Estimating/OsinLemma94PlanarPieces.lean`, 80790fad1) supersedes `OsinLemma94PlanarRunInput`.
  - `hmetric : OsinLemma94AntiparallelMetricStatement` is closed on main
    (`osinLemma94AntiparallelMetric`, e3da1ba60).
  - Open, with owners:
    - `OsinLemma94PolygonRealizationInput` (hull-unbound);
    - `OsinLemma94PolygonCountInput` (hull-count94);
    - `OsinLemma94CaseOneInput` (theoremc-retire);
    - `OsinLemma94CaseTwoInput` (sec5-sentences).
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
  - audit-sec5 landed that refutation at 3f6eaff76 (`VanKampen/RegionShellingSpurCounterexample.lean`)
    and queued it for wiring together with `FaceSetEarSpurCounterexample`; this lane has no objection.
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

## W1 (a) item 2: both sides of the collared walk (lead's ruling 09-13 ~06:30)
The lead dropped A, the weighted planar van Kampen lemma: dgo-analytic's `OsinPocketOuterPart`
(c0a1c1bee) already gives least area. B is not needed either, because nothing on the ruled route
consumes a shelling. Item C: kh-torsion owns two W1 (a) lemmas, the geodesic G-face collar along
short side arcs (item 1, `SurgeryGeodesicCollar`) and `IsDiscRegion` for both sides of the collared
closed walk `g₁ t₁ g₂ t₂` (item 2). This lane offered kh-torsion to take item 2, and kh-torsion took
it through `GeodesicCollarOutput` (`SurgeryGeodesicCollar`, e6d609771).

- `GGT/VanKampen/SimpleClosedWalkSides`: landed unverified at 79008d7e5. Probe 0913-070150-30707
  failed on two missing `classical` and one unused binder. After the fix, probe 0913-072751-55574
  is GREEN (BUILT), and `#audit_closed_axioms simpleClosedWalkSides` ⊆ {propext, Classical.choice,
  Quot.sound}. It then got a normal landing.
  - `IsSimpleClosedWalk M w`: the walk is nonempty, consecutive darts meet, the last dart returns to
    the first vertex, the vertices are distinct, and no edge is used in both directions.
  - `SimpleClosedWalkSidesStatement`: for a planar `M` there are complementary face sets, each an
    `IsDiscRegion`, with boundary cycles `w` and `w.reverse.map M.alpha`, both following their
    boundary walks. `theorem simpleClosedWalkSides`.
  - The proof:
    - The map on the walk's edges (`PredicateRestriction`) is connected.
    - So by `IsRestriction.faceOf_eq_of_faceClass`, no face class joins a walk dart to a reversed
      walk dart.
    - Each side's cycle follows its boundary walk (`followsBoundary_of_chain`), and
      `toDiscRegion_of_followsBoundary` gives `IsDiscRegion`.
  - `IsSimpleClosedWalk.reverseAlpha` exchanges the sides, so the exterior face can be put outside.
- The statement went to hull-select with the `PocketRegion` fit: `invDarts_outer_rotate` holds at
  `k = 0`, and both `FollowsBoundary` facts are the inputs of `GeodesicCollarStatement`.
- Not covered: pinched walks (a repeated vertex).
- `GGT/VanKampen/Estimating/OsinPocketRegionSimpleWalk`: landed unverified at a11a8d850; probe
  0913-074604-81036 is GREEN (BUILT), then a normal landing.
  - `PocketRegion.ofSimpleClosedWalk hw hout` builds the pocket from a simple closed walk `hw`,
    given `hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk`. The pocket's faces are the
    walk's side, its cycle is the walk, and its complement cycle is `walk.reverse.map alpha`.
  - `ofSimpleClosedWalk_invDarts_outer`: `invDarts Delta P.outer.cycle = walk`.
  - `ofSimpleClosedWalk_followsBoundary`: `P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary`.
  - `faceOf_mem_ofSimpleClosedWalk_faces` and `faceOf_alpha_not_mem_ofSimpleClosedWalk_faces`: the
    face of each walk dart is inside, and the face across it is outside.
  - Fit: this supplies the pocket `P` of kh-ejz's `MultipleEdgePocketRegionInput`
    (`Estimating/OsinPocketRegionSide.lean`) when the split walk `s₁ ++ invDarts A₁.darts ++ s₂ ++
    invDarts A₂.darts` is simple and the exterior face is off its side. Otherwise apply
    `reverseAlpha` first. Proving which side holds the exterior face, and placing the cells C, i, j,
    is left to the consumer.

## False-Prop binder sites (no deletions)
- `Embedded.FaceSetEarStatement` / `FaceSetEarDataStatement`: `VanKampen/FaceSetPeelProducer.lean:182`
  and `:194`, `Estimating/PieceConstruction.lean:30` and `:56`, `Estimating/PieceCore.lean:228`.
- `RegionShellingStatement`: `Estimating/PieceConstruction.lean:83`.

## Pocket pinch: `PocketPinchStatement` without `Collared` (lead's item, 09-13 ~09:40)
The piece order is pinch, then region, then collar (dgo-analytic, `Estimating/OsinPocketPieces.lean`,
b34e788e8). The consumers are kh-ejz (`PocketWalk.toPocketFaceSet`, 517cec238, which needs a simple
walk) and debt-conditional.

- **State on main (origin 13:27).**
  - `PocketPinchLabelledStatement` (dgo-analytic, bdc7337fd and cb0ec2d30) is the Prop the assembly
    uses. It takes the label binder `∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)` and
    `K.ClosedWalk` (walk order: chain and closes, vertices may repeat), and returns `∃ X' K', Nonempty
    (OEquivalentDiscDiagram X X') ∧ K'.Simple`. `Simple` is still `IsSimpleClosedWalk` of
    `K.boundary.cycle`.
  - kh-cckw (`Estimating/OsinPocketPinchUnpinched`, 33951a5b6, probe 0913-091746-34826) reduces
    `PocketPinchStatement` to `PocketPinchPinchedStatement`, the case `¬(K.boundary.FollowsBoundary ∧
    Unpinched X.toCombMap K.faces)`.
  - kh-cckw (`Estimating/OsinPocketUnpinchedEuler`, 74d4ebd34): if the boundary cycles of a face set
    and of its complement both follow the boundary, the face set is `Unpinched`.
  - dgo-geometric (`Estimating/OsinPocketPinchedTwoGonLobe`, 4181011af, unverified): the conclusion
    ties `K'` only to `D`, `eps`, `lo` and `hi`, so a lobe with fewer faces can serve a pinched pocket.
  - Landed since 13:44:
    - kh-cckw's E2 (9beb8f992);
    - cite-hull's `FaceSetCircuitNoncrossing` (67ec49f02);
    - dgo-analytic's builder `PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler`
      (`Estimating/OsinPocketRegionNoncrossingWalk`, 8bbf0a9c8).
  - dgo-geometric's model tests confirm both predictions.
    - Configuration A, on the pinched two-gon (e533e5581): the inner cycle fails and the outer
      follows.
    - Configuration B, on a two-petal rose (`Estimating/OsinPocketLakeModel`, 67e5b2f9c): the inner
      cycle follows and the outer fails.
- **Rulings since 615da4f77.**
  - R2 if kh-torsion confirms that no collar stage needs inner `FollowsBoundary`, else R1. B stays a
    residual under both. dgo-geometric model-tests A and B before either lands as a named Prop. The
    label binder is accepted.
  - Under R2 (lead ~13:40, pending kh-torsion), `Simple` becomes `∃ hw : IsNoncrossingClosedWalk
    X.toCombMap K.boundary.cycle, (hw.outerCycle X.planar).FollowsBoundary`. A needs no pinch, and B
    stays in the pinch Prop.
  - dgo-analytic (~14:05): the pinch hypothesis stays `K.ClosedWalk` under R1 and R2, since that is
    what the face set producer supplies (aa2df0eaa).
  - Evidence for R1, from dgo-analytic reading kh-torsion's collar proof route: the sector lemma
    uses inner `FollowsBoundary`. kh-torsion is asked to confirm. Under R1, `Simple` stays
    `IsSimpleClosedWalk`, and A and B both stay in the pinch Prop.
- **New module `Estimating/OsinPocketClosedWalkNoncrossing`** (probe 0913-133554-56930 green,
  landed with this report, unwired).
  - `BoundaryCycle.isNoncrossingClosedWalk`: every boundary cycle in walk order is an
    `IsNoncrossingClosedWalk`. Rotate from `alpha d` of a listed dart. The corner after `alpha d` lies
    in the face of `d`, and a dart off the edges of the listing keeps the next corner selected. So the
    first dart on an edge of the listing is a listed dart (`turn_mem_cycle`).
  - `PocketFaceSet.ClosedWalk.isNoncrossingClosedWalk` is the pocket form.
  - Consequence under R2: `K.Simple` is `K.ClosedWalk` plus outer `FollowsBoundary`. The turning
    condition does not choose how the walk pairs its darts at a repeated vertex.
- **Pairings at a repeated vertex.**
  - Around `v` the rotation reads `alpha d_1, [K], e_1, [gap], alpha d_2, [K], e_2, [gap], …`.
  - Inner following pairs `d_i → e_i`; outer following pairs `d_{i+1} → e_i`.
  - With two passages a walk pairs one way or the other. The inner pairing is B-like (outer fails),
    and the outer pairing is A-like (inner fails).
  - With three or more passages, `ClosedWalk` also allows pairings that follow neither side.
  - Consecutive darts of `t_1` meet through one corner of `Π`, and consecutive darts of `t_2` through
    one corner of `O`. So both arcs are outer-paired, and re-pairing to the outer order never splits
    them. Only side darts can move between `s_1` and `s_2`.
- **Obstructions** to splitting at a repeated vertex and keeping a simple lobe that holds a relator
  cell, at the landed generality. Neither is a proof or a refutation.
  - Side norms. A lobe whose side has a loop cut out keeps `length ≤ eps`, but not
    `wordNorm ≤ eps`: the loop's value is not 1 when it encloses relator cells. Fix: add the binder
    `∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)`, the consumer's `S.label_admissible`; then
    `wordNorm_le_length` gives norm ≤ length.
  - Configuration A, a notch. `∂Π` touches itself at `v` inside `t₁`, and the notch holds no
    relator cell.
    - The lobe with the relator cells has `t₁` with the loop removed, which is not a `CyclicArc`.
    - Every vertex split at `v` that separates Π's two corners adds a letter to the pocket face
      at `v`. `OEquivalentDiscDiagram` fixes relator-cell words, so this fails when that face is a
      relator cell.
    - The same happens inside `t₂` at a cut vertex of `X`.
    - A notch that holds a relator cell is harmless: it is a lobe with empty sides and an empty
      target arc.
  - Configuration B, the source in a lake. `x.rightSide` and `y.leftSide` touch behind Π.
    - `K.faces` is an annulus pinched at `v`, and Π lies in the inner complement component.
    - The only simple lobe `s₂[v..] t₂ s₁[..v]` has no cell arc, and its disc contains Π, so
      `rCellCount_lt` of the pocket cut can fail.
- **Proposal sent to dgo-analytic** (msg cdfe394e). The lead's ruling is under "Rulings since
  615da4f77".
  - (R1) Keep `PocketCarrier` and add the label binder. hull-respell proves the pinch outside A and
    B, and lands A and B as named Props.
  - (R2) Drop `PocketCarrier.inner_follows`.
    - A type-A pinch leaves the complement one circuit, so collapsing the complement alone already
      gives the enclosed diagram with the pinched walk as its boundary.
    - The transports use only `outer_follows`, but `GeodesicCollarStatement` uses both.
    - The pinch then handles lakes only.
- **Sub-piece handed to kh-cckw** (msg dc23c3a7), landed at 74d4ebd34: for a planar map, if the
  boundary cycle of `faces` and that of `facesᶜ` both follow the boundary, the face set is
  `Unpinched`.
  - Route: collapse both sides with `FaceSetCircuits.toDiscRegion`. The doubly collapsed map has 2
    faces, so `V = E_B`, and every boundary vertex is visited once.
  - This is the no-lake base case under either form.
- **Sub-piece E2 handed to kh-cckw** (msg 95934ab2), landed at 9beb8f992
  (`Estimating/OsinPocketPinchSplit`). `PocketFaceSet.pinchSplit K I hs` carries a pocket face set
  across a vertex split whose merged faces it avoids, with the same cycle, arcs and sides.
  `PinchSplit.Input.vertexOf_x_ne_y` puts the two split darts on different vertices.
- **Routes to the pinch.**
  - Lake absorption, in the case outside B (Π and the outer face lie in one complement component).
    Take `K' = K ∪ lakes`.
    - A lake meets no source dart, since Π is not in it, and no target dart, since the outer face
      is not in it. So its border consists of side darts only.
    - The new sides are the old ones with loops cut out, and the label binder bounds their norms by
      their lengths.
    - Then re-pair to the outer order at repeated vertices.
  - Explosion (R1), superseded by the route by steps below.
    - Thicken with `FaceEdgeDoubling`, `MonogonDoubling` and outer spur thickening (hs-vanishes,
      `SurgeryOuterSpurThickening`, 36ff632cd).
    - Split at gap corners (E2), induct to `Unpinched`, then apply `simple_of_followsBoundary`.
    - It needs inner `FollowsBoundary`, so the wrap case is left.
  - B stays a named residual under both forms. Under R1, A does too.
- **New module `Estimating/OsinPocketLakeAbsorption`** (probe 0913-141726-41707 green, landed with
  this report, unwired). It holds parts 1 and 2 of lake absorption.
  - `ExteriorComponent.component M faces o` is the set of faces reachable from the face `o` by face
    steps and by crossing edges that are off the boundary of `faces`. `absorbed M faces o` is its
    complement. It contains `faces` (`subset_absorbed`) and every lake.
  - `isBoundaryDart_absorbed_iff`: for `o ∉ faces`, a dart is a boundary dart of `absorbed` iff it
    is a boundary dart of `faces` whose reversal's face lies in the component of `o`.
  - `PocketFaceSet.absorb K hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem` gives a pocket face set on
    the absorbed faces with the same source, kept cell and arcs. It needs:
    - the source cell in the component of the exterior face;
    - a boundary listing `s₁ ++ invDarts sourceArc ++ s₂ ++ targetArc`;
    - `s₁ ⊆ firstSide` and `s₂ ⊆ secondSide`.
  - The length bounds pass to the sublists. `wordNorm_dartWord_le_length`, from the label binder,
    bounds each side's norm by its length.
  - Not proved: that the new listing can be taken in walk order. This is part 3, and it is open.
- **Route by steps along the walk's pairing** (proposed to the lead ~14:30, no ruling yet).
  - `K.ClosedWalk` pairs the darts at a repeated vertex `v`: each `alpha d` turns to the next dart
    `e` of the listing. `PinchSplit.Input` at darts `x`, `y` of `v` keeps darts, labels, relator
    words and the exterior word, and needs the two merged faces to be G-faces off the exterior.
  - Choose `x`, `y` so that every turn `alpha d ↦ e` at `v` stays on one side of the split. Then walk
    order survives (E2 carries `K`), and the repeated visits drop.
  - On an unpinched face set a pocket in walk order is simple (`simple_of_closedWalk_of_unpinched`),
    with no `FollowsBoundary`. So the route gives `Simple` under R1, and the weaker `Simple` of R2.
  - It reaches A and B once the corners at `v` are G-faces. In B the split merges a lake corner with
    an outer corner, and in A it merges corners inside `K`, which needs a variant of E2.
  - Needs:
    - thickening, so that the corners at `v` are G-digons;
    - E2 for a merge inside `K`;
    - at a vertex passed three or more times with a crossing pairing, no single split separates the
      turns, and re-pairing can move side darts between `s₁` and `s₂`. This case is not settled.
  - Proposed: one named residual `PocketPinchStepStatement` in place of named A and B, model-tested
    by dgo-geometric on the rose and the pinched two-gon.
- **New module `Estimating/OsinPocketPinchStep`** (probe 0913-143717-61429 green, landed with this
  report, unwired).
  - `PocketFaceSet.repeatedVisits K`: the darts of the boundary cycle less the vertices they start
    at.
  - `PocketFaceSet.simple_of_closedWalk_of_unpinched hK hpinch : K.Simple`, from `cycle_nonempty`,
    walk order, `unpinched_iff_nodup`, and `cycle_mem_iff` for `alpha_not_mem`.
  - `PocketPinchStepStatement`: for letter labels, `K.ClosedWalk` and `¬Unpinched X.toCombMap
    K.faces`, there are `X'`, `K'` with `Nonempty (OEquivalentDiscDiagram X X')`, letter labels on
    `X'`, `K'.ClosedWalk` and `K'.repeatedVisits < K.repeatedVisits`.
  - `pocketPinchLabelledStatement_of_step h : PocketPinchLabelledStatement`, by strong induction on
    `repeatedVisits`, composing with `OEquivalentDiscDiagram.trans`.
- **Sub-piece E4 handed to kh-cckw** (msgs 2d966898 and 7dcc7072): `pinchSplit` keeps `ClosedWalk`
  when no turn at the split vertex passes `x` or `y`, and `repeatedVisits` drops when two cycle darts
  land on the new vertices of `x` and `y`.
- **Ruling (roster, after 14:30): the route by steps is approved.** `PocketPinchStepStatement`
  replaces the named A and B. Until the step is proved, `pocketPinchLabelledStatement_of_step` is a
  reshape, not a discharge. Assignments:
  - kh-cckw: E4 (a)–(c);
  - go-lemma42: (ii), carrying `K` across a split that merges corners inside `K`;
  - (i), turning corners into G-digons: hull-respell checks `SurgeryFaceEdgeDoublingRegions` and
    outer spur thickening, and main assigns what is missing.
- **Landed since.**
  - kh-cckw's E4 (5b6b2b338, `Estimating/OsinPocketPinchSplitWalk`, probe 0913-151310-59486):
    `pinchSplit_closedWalk`, `pinchSplit_repeatedVisits_lt` and `_of_stretch`.
  - go-lemma42's (ii) (9acc804f2, `Estimating/OsinPocketPinchCarry`, unverified):
    `PocketFaceSet.pinchSplitInside` for `I.Inside K.faces`, and `exists_pinchStep_of_inside`, the
    conclusion of the step at such a split.
- **New module `Estimating/OsinPocketEdgeDoubling`** (probe 0913-154334-39978 green, landed with
  this report, unwired). This is item (i) for a relator-face corner outside `K`.
  - `PocketFaceSet.faceEdgeDoubling K f j hlen hf hs hsrc` takes `f ≠ X.outerFace`,
    `f ∉ K.faces` and `FaceEdgeDoubling.dart X f j ∉ K.sourceArc.darts`. It gives a pocket face set on
    `FaceEdgeDoubling.diagram X f j hlen hf` with the image faces and cells, and with the cycle, arcs
    and sides mapped by the dart embedding.
  - `faceEdgeDoubling_closedWalk hK` keeps walk order, and `faceEdgeDoubling_repeatedVisits` is an
    equality.
  - `FaceEdgeDoubling.label_letter`: letter labels survive (`label_admissible` at the symmetrized
    alphabet).
  - Helpers: `card_toFinset_map_eq_of_iff` and `DiscEmbeddingAway.boundaryCycle`.
  - Not covered: a doubled dart on the source arc, and a relator face inside `K` (the digon would
    join the face set).
- **Sub-piece T2 handed to kh-cckw** (msg 690b7740): `PocketFaceSet.outerSpurThickening` across
  `SurgeryOuterSpurThickening`, keeping walk order and repeated visits. `outerDarts_eq` does not
  apply there, so the target arc's start and `lo`, `hi` need a rebuilt position.
- **Open: S, the choice of split darts.** At a repeated vertex, choose `x` and `y` with these
  properties:
  - their corners are both outside `K` (E4) or both inside `K` ((ii));
  - they lie on distinct G-faces off the exterior;
  - every turn `alpha d ↦ e` at the vertex is a stretch that avoids `x` and `y`;
  - two cycle darts land on the new vertices.

  Obstacles: both corners in one face (double first), crossing pairings at a vertex passed three or
  more times, and a doubled dart on the source arc.

## Next
- Done: `SimpleClosedWalkSides` and the `HullSCOneStepQuasiGeodesicLeaves` docstring fix landed
  normally at 4dce22f1e (sec2-sentences informed). `SimpleClosedWalkSides` is on the wire queue.
  `OsinPocketRegionSimpleWalk` is consumed by dgo-analytic's `OsinPocketRegionOfSimple`.
- Done: `OsinPocketClosedWalkNoncrossing` (probe 0913-133554-56930), landed at 24ff94312.
  dgo-analytic is informed.
- Done: `OsinPocketLakeAbsorption` (probe 0913-141726-41707), landed at 49feec035.
- Done: `OsinPocketPinchStep` (probe 0913-143717-61429), landed at 8a7d46d90. It is a new file, so
  Rule 22 has no users to probe.
- Done: `OsinPocketEdgeDoubling` (probe 0913-154334-39978), landed with this report. It is a new
  file, so Rule 22 has no users to probe.
- Probe trap, now fixed. This lane's overlay listed `OsinAppendixGreendlingerParts.lean`, and the
  shared tree holds ghw-charp2's unlanded edit of that file (`loopCutInput`). Probe
  0913-140949-521 failed there. The file is off this lane's overlay list, and the rerun is green.
- Waiting on kh-torsion's confirmation of R1 or R2, and on kh-cckw's T2.
- Next: S, the split-dart choice at a repeated vertex, consuming E4, (ii) and (i), toward a proof of
  `PocketPinchStepStatement`.
- Parked: part 3 of lake absorption. The approved step route does not use it.
- Hold edits on `OsinAppendixGreendlingerParts` until ghw-charp2 lands 07b.
- Flip to `relativeGreendlingerQuasiGeodesicLeastArea_closed` as h94 and the parts land. A watcher on
  landed.log follows the part owners.
