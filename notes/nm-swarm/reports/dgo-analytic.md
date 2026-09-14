# Lane dgo-analytic (and helper H2 hull-assembly) — report

Non-MF verbatim formalization swarm, 2026-09-11; every-line swarm, 2026-09-13.

## 2026-09-13: `SectionPocketCutInput` from pieces

Rulings (lead, 09-13):

* ~04:05: this lane states the piece Props in `Estimating/OsinPocketPieces.lean`.
* ~05:00:
  * `SectionPocketCutInput` (`Estimating/OsinAppendixDescentCut.lean:71`) belongs to this lane.
  * `OsinDescentStepInput` is retired (a docstring note only).
  * `LoopCutInput` is on hold.
  * dgo-geometric model-tests each piece Prop.
* ~08:30: the pieces run in the order pinch, then region, then collar.
* ~09:15 (this lane, on kh-torsion's degenerate case): the collar takes `PocketCarrier.Nondegenerate`.
  The assembly proves it at least area (`nondegenerate_of_leastArea`).
* ~09:50:
  * LoopCut ruling (A) is final: `RespectsSections` gains `target ≠ some source` as its first conjunct.
  * ghw-charp2's patch 06a edits `OsinAppendixAssemblyDescent` lines 199-200 (`T.respects a …` becomes `(T.respects a …).2`); this lane holds edits on that file until ghw-charp2 reports landed.
  * Landed in f04929ebb with (A); the hold is released (rulings ~14:50).
  * hl-lemma46's `PocketRegion.exists_twoCollars_of_ne_or` (7eb17a3e9) covers the collar, modulo kh-torsion's `GeodesicCollarStatement`.
* ~10:15 (this lane, escalated to the lead): hull-respell's pinch obstructions, configurations A and B, with options R1 and R2 (see "The pinch obstructions" below). Awaiting the ruling and kh-torsion's answer on inner `FollowsBoundary`.
* ~10:30: kh-ejz's option (B) for `SectionPocketFaceSetInput`. The face set is produced on an O-equivalent copy of the optimal diagram, since on the optimal diagram the pocket walk can use both darts of one edge (a section backtrack between the two targets, or a gap-arc edge with the cell on both sides). hs-vanishes builds the spur thickening. This lane adds the label legality of the copy, because the pinch's label binder now applies to the copy.
* ~11:55: pinch ruling. R2 if kh-torsion confirms that its collar insertion does not need inner `FollowsBoundary`, otherwise R1.
  * B stays a residual under either option. Neither A nor B lands as a named Prop until dgo-geometric has model-tested it.
  * The label binder is accepted as a labelled Prop plus a weakening lemma.
  * Under R2, one Rule 22 co-probe restates `PocketRegionOfSimpleStatement`, `PocketCarrier`, the collar glue of 6cb3014e6, `GeodesicCollarStatement` (with kh-torsion) and `exists_twoCollars_of_ne_or` (with hl-lemma46). kh-ejz's `MultipleEdgePocketRegionInput` drops inner `FollowsBoundary` the same way; hull-select and kh-ejz hear when the form is fixed.
  * go-lemma42's `OsinPocketGlueDiagram` (f914f8728) takes only outer `FollowsBoundary` and is unaffected.
* ~12:10 (this lane, sent to the lead, landed with this report after probe 0913-125838-39384): walk order.
  * `BoundaryCycle` lists each boundary dart once, in any order, so `s_1 t_1 s_2 t_2` need not be consecutive along a walk. hull-respell's refill has no proof in that case.
  * `SectionPocketFaceSetInput` gives `∃ K, K.ClosedWalk` (chain and closes, without vertex injectivity), and `PocketPinchLabelledStatement` takes `K.ClosedWalk`.
  * `PocketFaceSet.Simple.closedWalk` shows that the simple output is in walk order.
  * dgo-geometric is asked to model-test the pinch without walk order.
  * kh-ejz's unlanded `PocketWalk.toPocketFaceSetOfNoncrossing` (`OsinPocketSectionFaceSet`) has the walk as its boundary cycle (`toPocketFaceSetOfNoncrossing_cycle`, `rfl`), so the `chain` and `closes` fields of `IsNoncrossingClosedWalk` supply `ClosedWalk`.
* ~15:30 (lead):
  * The hold on `OsinAppendixAssemblyDescent` is released. Patch 06a landed with (A) in f04929ebb, so this lane has nothing to land there.
  * Binder 5 (`OsinMultipleEdgePocketRegionSectionStatement`) is not written here until kh-ejz or the lead confirms the handover.
  * The model test of a multiple edge enclosing a lake goes ahead. It landed at 6e4ef1293; see "Binder 5 and a lake" below.

Target: a closed `DescentInput`, through `descentInput_of_sectionPocketCut`
(`Estimating/OsinAppendixDescentInduction`).

### Landed

* `Estimating/OsinPocketOuterPart.lean` (c0a1c1bee): the outer-part exchange for disc regions.
* `Estimating/OsinPocketRegion.lean` (497542415): `PocketRegion`, least area without shelling.
* `Estimating/OsinPocketPieces.lean`:
  * First statement, collar before pinch: 9cb70824c, probe 0913-073133-62116.
  * Restated in the ruled order: a032ab802, probe 0913-085713-52794, with the census row and the earlier report.
  * Nondegeneracy as the collar hypothesis, with `nondegenerate_of_leastArea`: b34e788e8.
* `Estimating/OsinPocketCollarOfGeodesic.lean`: `pocketCollarStatement_of_geodesicCollar : GeodesicCollarStatement → PocketCollarStatement`, probe 0913-100702-85407, 6cb3014e6 (unwired, wire-queued).
* `Estimating/OsinPocketRegionOfSimple.lean`:
  * The carrier `PocketFaceSet.toPocketCarrier`: a032ab802.
  * `pocketRegionOfSimple : PocketRegionOfSimpleStatement`, closed: c03054996, probe 0913-090829-84396.
* `Estimating/OsinAppendixAssemblyDescent.lean` (5957159598): the retirement note on `OsinDescentStepInput`.
  * Patch 06a (`(T.respects a …).2` at l.199) landed with ruling (A) in f04929ebb, and the disk copy equals main. Co-probe 0913-144505-9146 (GREEN, verdict line checked) compiled this file and the other ten modules of this lane, so nothing is re-probed.
* `Estimating/OsinPocketRegionNoncrossingWalk.lean` (8bbf0a9c8, probe 0913-140151-74557, unwired, wire-queued): `PocketRegion.ofNoncrossingClosedWalk`.
* `Estimating/OsinPocketCutResiduals.lean` (1b4053286, probe 0913-141538-35582, unwired, wire-queued): `sectionPocketCutInput_of_residuals` and `osinSectionPocketCutSection_of_residuals`, which pass the three closed pieces.
  * Restated after go-lemma42's `pocketCellTransport` (874a332a2; probe 0913-141750-43433 green, md5 equal to main). `hcell` is dropped, so both theorems pass four closed pieces. The two theorems had no Lean users. Probe 0913-142350-67007 green at base 538afe1ed, landed 5ef75ffa7.
* `Estimating/OsinDescentResiduals.lean` (5be777f16, probe 0913-142842-93848 green at base b8231e36d, unwired): `osinDescentSection_of_residuals h94 hloop hcount hregion hfaces hpinch hgeodesic : OsinDescentSectionStatement`, and `relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` with the same arguments.
  * It composes `osinDescentSection_of_pocketParts` with `osinMultipleEdgeCutSection_of_pieces hregion hgeodesic pocketCellTransport` and `osinSectionPocketCutSection_of_residuals hfaces hpinch hgeodesic`.
  * So the collar insertion is passed once, and nothing about the cell transport is left open.
  * theoremc-retire's T (48c6cc71e) adds `mu` to `UnboundInput` and threads `hbelow` into the `h94` binders. Its Rule 22 co-probe 0913-145812-91168 (verdict line `PROBE GREEN`) compiled this module, and the disk copy equals main.
* `Estimating/OsinPocketMultipleEdgeLakeModel.lean` (6e4ef1293, probe 0913-154539-52051 GREEN at base 282e779cb with 0 warnings, unwired, wire-queued): the model test of a multiple edge enclosing a lake. See "Binder 5 and a lake" below.

### The pieces, in the order of the assembly

| Prop | Owner | Shape |
|---|---|---|
| `SectionPocketFaceSetInput`, `OsinSectionPocketFaceSetSectionStatement` | kh-ejz (kept cell through hull-select's zero-cell merge, copy through hs-vanishes' spur thickening) | two distinct exterior regions to section `j` give a `PocketFaceSet` in walk order (`ClosedWalk`) of an O-equivalent copy of the optimal diagram whose labels are letters of `symmetricLabelAlphabet D` |
| `PocketPinchLabelledStatement`, implied by `PocketPinchStatement` | hull-respell | a `PocketFaceSet` in walk order (`ClosedWalk`) of a diagram with legal labels has an O-equivalent copy with a `Simple` one (boundary cycle `IsSimpleClosedWalk`), by simple circuits or a 0-refinement |
| `PocketRegionOfSimpleStatement` | dgo-analytic | a `Simple` face set gives a `PocketCarrier` (both cycles `FollowsBoundary`, sides of length and norm at most `ε`) |
| `PocketCollarStatement` | dgo-analytic from kh-torsion's `GeodesicCollarStatement` | a `Nondegenerate` `PocketCarrier` has an O-equivalent copy with a `Collared` carrier (sides admissible geodesic words) |
| `PocketCellTransportStatement`, `PocketOuterTransportStatement` | both closed: go-lemma42's `pocketCellTransport` (874a332a2) and hull-select's `pocketOuterTransport` (71d59592c) | regions of copies of the pocket to `t_1` and `t_2` glue back, target `OsinMultipleEdgeCut.ofPocketRegion` |

Assembly, proved:

* `PocketCarrier.nondegenerate_of_leastArea`: a carrier in a least-area diagram is nondegenerate.
* `PocketCarrier.nonempty_osinSectionPocketCut`: a collared carrier gives the cut.
* `sectionPocketCutInput_of_pieces hpinch hregion hcollar hcell houter`.
* `osinSectionPocketCutSection_of_pieces`.
* `sectionPocketCutInput_of_residuals hpinch hgeodesic` and `osinSectionPocketCutSection_of_residuals hfaces hpinch hgeodesic` (`Estimating/OsinPocketCutResiduals`). They pass `pocketRegionOfSimple`, `pocketCollarStatement_of_geodesicCollar hgeodesic`, go-lemma42's `pocketCellTransport` and hull-select's `pocketOuterTransport`. So the section pocket producer takes exactly the three open Props below.

### The region piece

`Estimating/OsinPocketRegionOfSimple.lean` builds the carrier over `PocketRegion.ofSimpleClosedWalk`:

* `PocketFaceSet.toPocketCarrier K hK hfaces` and `nonempty_pocketCarrier_of_sideFaces_eq`.
* The side of the walk is the pocket.
* Both cycles follow the boundary (`ofSimpleClosedWalk_followsBoundary`).
* The inverse complement cycle is the walk (`ofSimpleClosedWalk_invDarts_outer`), so the split carries over.
* Given `sideFaces X.toCombMap K.boundary.cycle = K.faces`, the kept cell stays inside and the source cell outside.

The equality is a general map lemma, handed to hull-component, and landed by it (d20913c51, unverified, wire-queued):
`SimpleClosedWalkSides.sideFaces_boundaryCycle_eq (hM : M.IsConnected) (boundary : BoundaryCycle M faces) (hf : f ∉ faces)`,
in the new module `GGT/VanKampen/SimpleClosedWalkSideFaces.lean`.

* sideFaces ⊆ faces: by EqvGen induction; crossing an edge off the walk keeps membership.
* faces ⊆ sideFaces: the rest of the face set is closed under `alpha` and `sigma`, so connectivity rules it out.

Closed: `pocketRegionOfSimple : PocketRegionOfSimpleStatement`.
It goes through `PocketFaceSet.sideFaces_boundary_cycle_eq_faces`, applied at `CombMap.connected_of_planar _ X.planar` and `K.outerFace_not_mem`.
Probe 0913-090829-84396 GREEN, `#audit_closed_axioms` ⊆ {propext, Classical.choice, Quot.sound}.

hull-component has no further sub-piece here and was told to ask the lead (~09:15).

### The collar piece

`Estimating/OsinPocketCollarOfGeodesic.lean` proves `pocketCollarStatement_of_geodesicCollar : GeodesicCollarStatement → PocketCollarStatement`.

* `exists_collaredWord D g`: a geodesic word in the letters of `D` of value `g`, from `GGT.OsinComponents.existsGeodesicWord`.
* The collar insertion needs an inverse closed base and every label a letter. Neither holds for an arbitrary `D` and diagram, so it runs at `allLettersRelGenSet G Lambda`, whose base and subgroups are all of `G`. The collars still read the geodesic words of `D`.
* `Nondegenerate` is the hypothesis `hne` of `PocketRegion.exists_twoCollars_of_ne_or`: arc `t_1` is `invDarts X K.sourceArc.darts`, and `t_2` is `K.targetArc.darts`.
* The new carrier:
  * the cells `source` and `kept` move along `E.cellIndex`, and stay on their sides of the pocket;
  * the source arc is carried through the cell darts outside the pocket, and the target arc through the outer darts (`CyclicArc.mapTo`);
  * the sides are the collars. Each side is as long as the norm of the old side value, which is at most `ε`, and keeps that value.
* `Collared` is then the geodesic words' admissibility and lengths.

Probe 0913-100702-85407 GREEN, `#audit_axioms` ⊆ {propext, Classical.choice, Quot.sound} on all six declarations.

### The degenerate carrier

kh-torsion's case: both arcs are empty and both sides have value 1.

* `Collared` forces geodesic side words, which are empty here.
* So the collared boundary cycle would be empty, and the collar cannot be proved for this carrier.

The fix:

* `PocketCarrier.Nondegenerate K`: `0 < K.sourceArc.length ∨ 0 < K.targetArc.length`, or a side value `≠ 1`.
* `PocketCollarStatement` takes `K.Nondegenerate`.
* `nondegenerate_of_leastArea (hlea : X.LeastArea) K`: otherwise `diagram_boundaryWord` and the split make the pocket read `s_1 s_2` of value 1.
  * `IsRelatorProduct.one` fills it, so `diagram_leastArea` gives `rCellCount ≤ 0`.
  * That contradicts `diagram_rCellCount_pos` at the kept cell.
* The assembly applies it at `(S.equiv.trans E₁).leastArea hlea`, so no residual Prop is added.

### The pinch obstructions (hull-respell, escalated ~10:15)

hull-respell's analysis is in `notes/nm-swarm/reports/hull-respell.md`, section "Pocket pinch". Neither configuration below is a proof or a refutation, and neither is model-tested yet.

* Side norms. A lobe that cuts a loop out of a side keeps `length ≤ ε` but not `wordNorm ≤ ε`. The fix is the binder `hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)`, after which `wordNorm_le_length` and `symmetricLabelAlphabet.carrier_eq` give norm ≤ length.
  * Accepted by this lane. The consumer supplies it as `S.label_admissible` (`OsinAppendixSections.lean:272`, `RealizedRegionFamily.LabelLegal`).
  * Done together with ruling (B), and landed with this report: `PocketPinchLabelledStatement` and `pocketPinchLabelledStatement_of_pocketPinchStatement` in `OsinPocketPieces`, with the assembly switched to them. No peer file breaks, and `OsinPocketPinchUnpinched` still builds against `PocketPinchStatement`.
* Configuration A, a notch. `∂Π` touches itself at a vertex `v` inside the source arc `t_1`, or `∂X` does at a cut vertex inside `t_2`, and the notch holds no relator cell.
  * In the lobe that holds the relator cells, `t_1` with the loop removed is not a `CyclicArc`.
  * A vertex split at `v` adds a letter to `Π`, which `OEquivalentDiscDiagram` forbids.
* Configuration B, a lake. The source cell lies in a lake. `K.faces` is an annulus pinched at `v`, and the only simple lobe has no cell arc and contains `Π`.

What the carriers use:

* `PocketCarrier.inner_follows` is used only by the collar, as both a hypothesis and an output of `GeodesicCollarStatement` and `exists_twoCollars_of_ne_or`.
* `nonempty_osinSectionPocketCut` and the transports use only `outer_follows`.
* Elsewhere, hull-select's zero-cell merge (`OsinPocketZeroCellMerge`) and kh-ejz's `MultipleEdgePocketRegionInput` also use inner `FollowsBoundary`, but outside this cut.

Options put to the lead:

* R1: keep the carrier, and land A and B as named residual Props (`PocketNotchStatement`, `PocketLakeSourceStatement`) once dgo-geometric has model-tested them.
* R2: drop `inner_follows` and weaken `PocketFaceSet.Simple` to match, so that A goes away.
  * This restates `PocketRegionOfSimpleStatement`, `PocketCarrier`, `pocketCollarStatement_of_geodesicCollar`, kh-torsion's `GeodesicCollarStatement` and hl-lemma46's `exists_twoCollars_of_ne_or`.
  * It works only if kh-torsion's insertion does not need inner `FollowsBoundary`; kh-torsion has been asked.
* B stays a residual under either option.
* Recommendation: R2 if kh-torsion confirms, otherwise R1.

hull-respell's smallest diagrams (~11:50):

* A (notch, `eps = 0`) and B (lake, `eps = 2`) each have an O-equivalent rebuild with a simple face set, and neither rebuild needs a 0-edge.
* Neither rebuild is a local vertex split. Each realizes the pocket walk as a simple polygon and refills the rest with `G`-faces that read duplicated edge letters back and forth, so their values are 1.
* The general refill was open when the boundary listing is not a closed walk. cb0ec2d30 requires walk order, so that case no longer reaches the pinch.

R2 with kh-ejz's `IsNoncrossingClosedWalk` (26a7858f2) as `Simple` (~13:20, sent to the lead):

* At a vertex `v` the walk passes twice, the walk darts around `v` read `d_1, e_1, d_2, e_2` (passage `i` is `d_i` then `e_i`).
  * The side whose sectors lie inside the passages follows its boundary at `v`: rotating from `d_i` through its own sector meets `e_i`.
  * The other side crosses a sector and meets a dart of the other passage, so it does not follow.
* Configuration A has the pocket sectors between the passages, so inner fails and outer follows. This matches `OsinPocketPinchedTwoGonRegion.not_followsBoundary`.
* Configuration B has the pocket sectors inside the passages, so outer fails.
* The transports and `nonempty_osinSectionPocketCut` need `outer_follows`. Under R2, `Simple` is therefore `∃ hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle, (hw.outerCycle X.planar).FollowsBoundary`. A needs no pinch, and B stays in the pinch Prop.
* New lemma, for this lane: the inner `IsDiscRegion` has to come from `toDiscRegion_of_euler`, that is, χ of the reclosed map of `sideFaces` along a noncrossing walk equals χ of the ambient map. Only the pinched model has it (`innerMap_euler`, by `decide`).
* dgo-geometric is asked to check the prediction on the pinched two-gon model and on hull-respell's smallest A and B.
* Lead ruling (~13:40, still pending kh-torsion's answer): under R2, `Simple` is `∃ hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle, (hw.outerCycle X.planar).FollowsBoundary`. A needs no pinch, B stays in the pinch Prop, and cb0ec2d30 stands.
* Handed to hull-euler: the Euler lemma, `(reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic = M.eulerCharacteristic` for a noncrossing `w` whose outer cycle follows. This lane keeps `PocketRegion.ofNoncrossingClosedWalk` and the restatement co-probe.
* Evidence for R1 (kh-torsion asked to confirm):
  * `GeodesicCollar.StripStatement` (a89b55a0d, `SurgeryGeodesicCollarAssembly.lean:190`) takes `IsSimpleClosedWalk (s ++ rest)`.
  * From a pocket region that walk comes only from `PocketRegion.isSimpleClosedWalk_invDarts_outer P hin hout`, which uses inner FollowsBoundary.
* hull-euler (~13:55, checked by hand here): the Euler lemma is false without outer following.
  * Counterexample: a three-petal rose, darts 0..5, `alpha = (0 1)(2 3)(4 5)`, `sigma` 1→0→3→2→5→4→1, χ = 2.
  * `w = [0,2,4]` satisfies `IsNoncrossingClosedWalk` (`turn_mem` at m = 1), but its three passages cross pairwise at the vertex, and the inner reclosed map has χ = 0.
  * `turn_mem` rules out crossing only at vertices passed twice.
  * The lemma therefore takes `(hw.outerCycle hM).FollowsBoundary`, which R2's `Simple` carries.
  * Route: χ(N_in) + χ(N_out) = χ(M) + 2, and the outer side preserves χ.
* hull-respell (~14:05, probe 0913-133554-56930): `Estimating/OsinPocketClosedWalkNoncrossing` proves `PocketFaceSet.ClosedWalk.isNoncrossingClosedWalk` via `BoundaryCycle.turn_mem_cycle`.
  * Every listing in walk order is noncrossing in kh-ejz's sense, so the `∃ hw` in R2's `Simple` is free. Checked here: rotating from `alpha d` stays in selected faces until it meets a listed dart.
  * The pinch hypothesis stays `K.ClosedWalk` under R1 and R2. That is what the face set producer supplies (aa2df0eaa), and inner FollowsBoundary has no producer.
  * The pinch therefore re-pairs at vertices passed three or more times, as in the rose. If that can fail, the face set output is strengthened with kh-ejz, not the pinch hypothesis.
* Lead rulings (~13:40 and ~14:00):
  * hull-euler builds `NoncrossingClosedWalkEuler`: `IsNoncrossingClosedWalk.reclosed_euler`, with outer following as a hypothesis, model-tested on the rose.
  * This lane drafts the noncrossing-walk region builder over hull-euler's signature and lands it unwired.
  * The restatement co-probe (`Simple`, `PocketRegionOfSimpleStatement`, `PocketCarrier`, the collar) waits for a green Euler lemma and no port failure from fff-quotient.
  * Q2: this lane states the zero-cell merge on the copy (roster l.405 and l.617).
    * sec2-sentences' kept cell (`Estimating/OsinPocketKeptCell`, 492057fb6) is stated on the diagram of the thickened family `S'` of hs-vanishes' `OuterSpurThickeningStatement`. `OEquivalentDiscDiagram` keeps no darts, so nothing is transported: the merge on that copy is `zeroCellPocketMerge` at `S'`.
    * `exists_kept_of_pocketRegion` takes a `PocketRegion` with `hinner : P.inner.cycle = K.walk` and no `FollowsBoundary`. A pinched pocket walk whose outer cycle follows (Configuration A) therefore gets its kept cell from `exists_kept_of_pocketRegion … (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler) rfl havoid`, once hull-euler's lemma supplies `heuler`. This is blocker 1 of the ~14:05 rulings, so the Euler lemma is needed under R1 as well (hull-euler told).
    * On origin/main only `OuterSpurThickeningStatement` outputs a family, and it is now proved (`outerSpurThickening`, 36ff632cd). The copies for (b), a gap-arc edge with the cell on both sides, and for (c) have no statement. Only there would a merge stated on a family's diagram not apply. Scope sent to the lead.
    * Ruled ~14:20 (roster l.971-973): no new merge Prop. Copies (b)/(c) take `OuterSpurThickeningStatement`'s output shape, so the kept-cell theorem applies on `S'`. Blocker 1 is split: `hout` and `hfollows` go to hull-select, `heuler` to hull-euler, `havoid` to sec2-sentences.
* Builder (this lane): `Estimating/OsinPocketRegionNoncrossingWalk`, `PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler`.
  * The inner region comes from `toDiscRegion_of_euler` and the outer from `toDiscRegion_of_followsBoundary`. The inverse complement cycle is the walk.
  * `heuler` has the type of the conclusion of hull-euler's lemma, so the co-probe passes `hw.reclosed_euler X.planar hfollows` and nothing unlanded is imported here.
  * hull-euler's `IsNoncrossingClosedWalk.reclosed_euler hw hM hout` (`NoncrossingClosedWalkEuler`, landed unverified 7e254eb66) has exactly that type at `M := Delta.toCombMap` and `hM := Delta.planar` (checked by reading). Its first probe, 0913-145807-90519, read `PROBE FAILED rc=1`. The re-landed 19866c7d6 is on main, and its probe 0913-150114-7274 has the verdict line `PROBE GREEN`. So the gate "green Euler lemma" is met, and the restatement co-probe now waits only for kh-torsion's R1/R2 answer.
  * Model test (dgo-geometric, 80df00345, `Estimating/OsinPocketPinchedTwoGonNoncrossingRegion`, landed unverified): on the pinched pocket cycle `[5,3,4,6]` all four hypotheses hold together, and the region's inner cycle neither follows nor is simple. So the builder covers Configuration A, which `PocketRegion.ofSimpleClosedWalk` does not.
* Further evidence for R1: kh-torsion's 5197fa6fc (`SurgeryGeodesicCollarWalk`) carries simple closed walks through the edge insertion and the vertex pinch.
* dgo-geometric's e533e5581 (probe 0913-134649-6539, green) confirms Configuration A on the pinched two-gon. The inner cycle fails, the outer follows, and under R2's `Simple` that pocket needs no pinch.
* dgo-geometric's 67e5b2f9c (`Estimating/OsinPocketLakeModel`, probe 0913-140543-86239 green, md5 equal to main) confirms Configuration B on a two-petal rose. The walk `[0,2]` is noncrossing but not simple, the inner cycle follows and the outer does not. So A and B are both model-tested.
* R1 evidence from kh-torsion's own report ("Proof route" of the geodesic collar, on main). The sector lemma uses inner and outer `FollowsBoundary` with `invDarts outer ~r inner` to show that the circuit revisits no vertex. That is a step using inner `FollowsBoundary`, so the ~11:55 ruling gives R1. kh-torsion is asked to confirm.
  * Under R1, `Simple` stays `IsSimpleClosedWalk`, `PocketCarrier` keeps `inner_follows`, and no restatement co-probe runs. A and B stay in the pinch Prop.
  * No answer by 15:00. The roster (l.889) leaves the decision to kh-torsion. One follow-up was sent, citing `SurgeryGeodesicCollar.lean:71` (inner `FollowsBoundary` is a hypothesis) and kh-torsion.md:246 (the sector lemma).
  * `PocketRegion.ofNoncrossingClosedWalk` still serves the kept cell of a pinched walk (Q2 above).
  * It does not serve jacobson's loop cut under R1. `nonempty_osinLoopCut_of_pocketRegion` (`Estimating/OsinPocketLoopCut`, 70f8cd913) takes `hin : P.inner.FollowsBoundary` (:209) for `exists_twoCollars_of_ne_or` (:228), and the builder supplies only outer following. So under R1 a non-simple Case 1 walk reaches the loop cut only through a pinch (jacobson, ~14:35).
    * Put to the lead at 15:00. Under R1, hull-select's four-facts producer (roster l.963) serves the kept cell but not this R-cell branch, which is still at 70f8cd913 with `hin` at :209 and :228. That branch then needs a simple walk (the pendant-path check of roster l.949) or the pinch.
    * The branch stays on the waist's path through binder 2, jacobson's `OsinLemma94CaseOneSameCellStatement`, even though `LoopCutInput` is closed.
* R2 co-probe list, if R2 is ruled. `exists_twoCollars_of_ne_or` has four users: `OsinPocketCollarOfGeodesic`, `OsinPocketMultipleEdgeAssembly`, `OsinPocketTwoCollars` and `OsinPocketLoopCut`.
  * jacobson writes its own hunk at co-probe time, deleting the binder at :209 and the argument at :228. Nothing is staged on disk before then.

### Binder 5 and a lake (model test, 6e4ef1293)

`Estimating/OsinPocketMultipleEdgeLakeModel` tests the outer clause of kh-ejz's `MultipleEdgePocketRegionInput`: `C.face ∈ P.faces`, `(cell i).face ∉ P.faces`, `(cell j).face ∉ P.faces` and `P.outer.FollowsBoundary`.

* The map `M` has 8 darts, with `alpha = (0 1)(2 3)(4 5)(6 7)` and `sigma` sending `0,…,7` to `1,2,6,5,0,7,4,3`. It has 2 vertices, 4 edges and 4 faces, so χ = 2 and `planar` holds (`OrbitClassifier.orbitEquiv`, `decide`).
* Its faces are the pocket `K = [0,2,5]`, the lake `Π_i = [1]` (a monogon inside the loop `{0,1}`), `Π_j = [4,7]` and `O = [3,6]`.
* `isNoncrossingClosedWalk_pocketCycle` and `pocketCycle_not_isSimpleClosedWalk`: the walk `[0,2,5]` is noncrossing and passes the vertex `v` twice.
* `pocketCycle_innerCycle_followsBoundary` and `pocketCycle_outerCycle_not_followsBoundary`: the inner cycle follows its boundary and the outer cycle does not, as in Configuration B.
* `not_followsBoundary_of_monogon` (general): suppose a face set has a boundary dart `y` with `facePerm y = y` and a second boundary dart. Then none of its boundary cycles follows its boundary. The boundary walk from `facePerm y = y` cannot move, because `y` is not internal, while `boundaryPerm` moves `y`.
* `lake_not_followsBoundary`: no face set that contains `Π_i` and `Π_j` but not `K` has a following boundary cycle. `PocketRegion.outside` is the complement of `faces`, so no `PocketRegion` of `M` with `K` inside and `Π_i`, `Π_j` outside has `P.outer.FollowsBoundary`.
* The endpoint `multipleEdgeLakePrediction : MultipleEdgeLakePrediction` is under `#audit_closed_axioms`.

Consequences (map level only; the model has no labels, cells or sections):

* The model rules out one choice of `P`. A pocket region with `K` inside, whose complement makes `Π_i` a lake, has no following outer cycle.
* Correction (~16:05, from audit-sec5): this does not refute binder 5.
  * `MultipleEdgePocketRegionInput` (`OsinPocketRegionSide.lean:49`) and hull-select's copy draft (`drafts/hull-select-RegionSide-copy-r1.lean`, l.58-69) both let the producer choose `P`, `C`, `s₁`, `s₂`, `A₁` and `A₂`.
  * My earlier line "binder 5 as stated has no witness" was too strong. It went to the lead, hull-select and kh-ejz, and each has been sent the correction.
* audit-sec5's reading of the model:
  * `Π_i` is a lake of `P = a ∪ gap ∪ b` exactly when the arcs of `a` and `b` on `Π_i` meet at a vertex on the far side.
  * In the model both joins have arcs of length 0 on `Π_i`: the trivial path at `v` and the edge `{2,3}`. `RealizedSectionFamily.nondegenerate` (`OsinAppendixSections.lean:251`, `0 < sourceArc.length ∧ 0 < targetArc.length`) forbids that.
  * So the model rules out only `a ∪ gap ∪ b` in that configuration.
* audit-sec5's choice of `P` is the gap alone, with the faces of `a` and `b` outside.
  * `s₁` is the inverse of the side of `a` facing the gap, `A₁` is the gap arc of `Π_i`, `s₂` is the inverse of the side of `b`, and `A₂` is the gap arc of `Π_j`. Lengths and norms are unchanged.
  * Its sketch that this `P` has no lake has three steps:
    * the ring `Π_i ∪ a ∪ Π_j ∪ b` is dual-connected, by the nondegenerate arcs;
    * the partner of every boundary dart of `P` is a ring face;
    * `exists_boundaryDart_dualConnected` (`FaceSetDualReach.lean:77`) puts a ring face in every component of the complement.
  * This lane checked that the cited declarations exist and that `P` is existential in both forms. The sketch itself is audit-sec5's.
* No lake is necessary for outer following but not sufficient. What still blocks the gap-only `P` is simplicity, that is, the pinch. In audit-sec5's configuration (b'), a spur on `Π_i` between `C1` and `C2`, each longer than `2ε`, defeats every `P`.
* `hout` is load-bearing:
  * `nonempty_osinMultipleEdgeCut_of_pocketRegion` (`OsinPocketMultipleEdgeAssembly.lean:88`) takes it at l.96 and passes it at l.120 and l.188.
  * `OsinPocketTwoCollars` takes it at l.60 and passes it at l.96.
* So a producer of binder 5 should take the gap-only pocket, not `a ∪ gap ∪ b`. audit-sec5 sees nothing in a globally distinguished section family that rules out the lake for `a ∪ gap ∪ b`, short of Lemma 9.7(b) itself.

### The wrap refutation of the pinch at ε = 0 (dgo-geometric, 6dfa779fe and 87358b0ad)

`Estimating/OsinPocketWrapRose` proves `pocketPinchWrapRefutation : ¬ PocketPinchStatement.{0,0,0} ∧ ¬ PocketPinchPinchedStatement.{0,0,0} ∧ ¬ PocketPinchLabelledStatement.{0,0,0} ∧ ¬ PocketPinchStepStatement.{0,0,0}`, under `#audit_closed_axioms`. Probe 0913-163031-39703 (base bbf968910) has the verdict line `PROBE GREEN` and lists both modules, and its md5s equal main.

* The model is a three-petal rose: darts 0..5, one vertex. Its faces are the `G`-cell `κ = [0,2,4]`, the relator cells `Π = [1]` (reading `x`) and `R = [5]` (reading `y`), and the exterior `[3]`. Every label is a letter.
* `wrapK : PocketFaceSet D 0 wrapDiagram 0 1` has faces `{κ, R}`, source `Π`, kept `R`, empty sides, `t_1 = ∂Π` and `t_2 = ∂X`. Its cycle `[0,2]` is in walk order and follows the boundary.
* `PocketWrap.no_simple_of_oEquivalent_monogons`: when the relator words and the boundary word have one letter each, no O-equivalent copy has a simple pocket face set at `ε = 0`, in any positions.
* Checked here against the statements (`OsinPocketPieces.lean:260`, `:272`): the pinch Props range over every `eps : ℕ` and every `W`, with no small-cancellation binder. So `ε = 0` and one-letter relators are admissible.
* Consequence: `hpinch` in `sectionPocketCutInput_of_pieces`, `sectionPocketCutInput_of_residuals`, `osinSectionPocketCutSection_of_residuals` and `osinDescentSection_of_residuals` is false at `0, 0, 0`. The residual has to be restated, and the lead rules the form (sent ~16:40).
* Both candidate repairs cost nothing at the consumer:
  * `0 < eps`: `osinSectionPocketCutSection_of_pieces` takes `eps0` from the face set producer and can take `max eps0 1`.
  * Long relators, for instance `∀ v ∈ W, 2 * eps < v.length`: `hcondition.long` gives `rho ≤ v.length`, and `rho0` is chosen after `eps`, so `max rho0 (2 * eps + 1)` supplies it.
  * dgo-geometric's rescue at `ε ≥ 1` is `K' = {R}`, whose boundary `[5]` is one side. It needs a relator no longer than `2ε`, so long relators exclude the model at every `ε`.
  * Whether either form is true is not known. The chosen form needs a model test before it lands.
* Users of the four pinch Props, for the Rule 22 co-probe:
  * this lane: `OsinPocketPieces`, `OsinPocketCutResiduals`, `OsinDescentResiduals`;
  * `OsinGreendlingerOpenResiduals` (ghw-assembly, hull-select);
  * `OsinPocketPinchStep` (hull-respell), `OsinPocketPinchUnpinched` (kh-cckw), `OsinPocketPinchCarry` (go-lemma42), `OsinPocketLakeLabelledModel` (audit-sec3);
  * dgo-geometric's `OsinPocketPinchedTwoGonLobe`, `OsinPocketPinchedTwoGonOuterFollows`, `OsinPocketWrapMonogon` and `OsinPocketWrapRose`.

### Truth caveats sent to dgo-geometric for model tests

The earlier list covers:

* side trimming;
* the norm bound;
* the collar;
* the pinch case;
* empty sections;
* the outer base dart.

New with the ruled order:

* A 0-refinement that makes the pocket boundary vertex-simple must keep the boundary word of `X` (O-equivalence) and the side lengths.
* Splitting a vertex across inner corners, with a 0-edge between `G`-faces, does both.
* The collar under `Nondegenerate`: with empty arcs and only one side of value `≠ 1`, the collared boundary is that side's geodesic word alone.
  * Tested (dgo-geometric, ~16:50, on paper, no Lean): no refutation, and the case occurs.
    * `pocketCollarStatement_of_geodesicCollar` through `exists_twoCollars_of_ne_or`: both `hne` hypotheses hold, and the collared carrier reads the one nonempty geodesic word. An empty second collar costs nothing downstream.
    * The weight is on `GeodesicCollarStatement` (kh-torsion) in its removal sub-case: `s` nonempty of value 1, `g = []`, `rest ≠ []`. The new cycle `rest.map ι` is closed, so the copy has to identify the endpoints of `s`. The output allows this, because `ι` keeps `alpha`, the labels, `outerDarts`, the darts of the outside cells and the cell sides, but not the rotation.
    * The model: `G = Multiplicative ℤ`, 6 darts, kept `[d1,e1]`, source `[αd1,c]`, exterior `[αe1,αc]`. `s_1 = [d1]` has value 1 and distinct endpoints, `s_2 = [e1]` has value `≠ 1`, and both arcs are empty.
    * The copy has one vertex and the faces kept `[d,e]`, source `[f,c]`, exterior `[αe,αc]`, plus the monogon `G`-faces `[αd]` and `[αf]`. `P'' = {kept, [αd]}` has cycles `[e]` and `[αe]`.
    * `ι` sends `d1 ↦ αf`, `αd1 ↦ f`, `e1 ↦ e` and `c ↦ c`. So the source face `[f,c]` is the image of `[αd1,c]`.
    * Checked here: the face permutations and both Euler counts (2−3+3 and 1−4+5), that both cycles of `P''` follow the boundary, and that `invDarts P''.outer.cycle = [ι e1]`.
    * Not checked by dgo-geometric: a side that repeats a vertex.

### Residual Props of `DescentInput` on this route

* `OsinSectionPocketFaceSetSectionStatement` (kh-ejz).
* `PocketPinchLabelledStatement` (hull-respell), or `PocketPinchStatement` through the weakening lemma. kh-cckw reduced the unlabelled one to `PocketPinchPinchedStatement` (33951a5b6). Configurations A and B are escalated.
  * False as stated at universes `0, 0, 0` (dgo-geometric's wrap model, 6dfa779fe). See "The wrap refutation of the pinch" above; the restated form is awaiting the lead's ruling.
  * hull-respell's `pocketPinchLabelledStatement_of_step` (`Estimating/OsinPocketPinchStep`, 8a7d46d90, unwired) reduces the labelled one to `PocketPinchStepStatement`, by strong induction on repeated visits. The step: a pinched pocket in walk order, in a diagram whose labels are letters, has an O-equivalent copy whose labels are letters, with a pocket in walk order and fewer repeated visits.
* `GeodesicCollarStatement` (kh-torsion, `SurgeryGeodesicCollar.lean:67`), in place of `PocketCollarStatement`.
* `PocketCellTransportStatement` and `PocketOuterTransportStatement` are closed, both under `#audit_closed_axioms`:
  * go-lemma42's `pocketCellTransport` (`Estimating/OsinPocketGlueCellTransport`, 874a332a2, probe 0913-141750-43433);
  * hull-select's `pocketOuterTransport` (`Estimating/OsinPocketGlueOuterTransport`, 71d59592c).
  * `Estimating/OsinPocketCutResiduals` passes both, together with `pocketRegionOfSimple` and the collar from `GeodesicCollarStatement`.
* Outside `SectionPocketCutInput`, `descentInput_of_sectionPocketCut` still takes `LoopCutInput`, `MultipleEdgeCutInput`, `EulerCountInput`, `UnboundInput` and `O52LeastAreaStatement`. After (A), `LoopCutInput` is closed by `loopCutInput` (`OsinAppendixSectionInduction`), which is vacuous because `RespectsSections` excludes loops.
* Uniformly in the parameters (`Estimating/OsinDescentResiduals`), `OsinDescentSectionStatement` takes seven Props, six of them open:
  * `OsinLemma94SectionStatement` (hull-unbound, hull-count94);
  * `OsinLoopCutSectionStatement`, closed after (A) by `osinLoopCutSection` (`OsinAppendixGreendlingerParts.lean:74`, under `#audit_closed_axioms`). The binder stays because ghw-assembly's waist passes the producer (rulings ~14:50), so no Rule 22 restatement runs here;
  * `OsinPhiPrimeCountSectionStatement` (hull-euler, `osinPhiPrimeCountSection_of_pieces`);
  * `OsinMultipleEdgePocketRegionSectionStatement` (kh-ejz);
  * the three pocket residuals: `OsinSectionPocketFaceSetSectionStatement`, `PocketPinchLabelledStatement`, `GeodesicCollarStatement`.
  * O52 is `Embedded.o52LeastArea`, and the cell and outer transports are closed.

Closed here:

* `PocketRegionOfSimpleStatement` (`pocketRegionOfSimple`).
* The nondegeneracy of carriers at least area (`nondegenerate_of_leastArea`).
* `PocketCollarStatement` from `GeodesicCollarStatement` (`pocketCollarStatement_of_geodesicCollar`, through hl-lemma46's two collars).

Since T (48c6cc71e), `OsinLemma94SectionStatement` assumes clause (b) of Lemma 9.7 below the cell count, and `UnboundInput` takes `mu`. The six open Props are otherwise unchanged. The lake model adds no Prop. It rules out one choice of pocket for binder 5, and audit-sec5's gap-only pocket avoids it.

### Next (16:40)

* The pinch restatement, once the lead rules between `0 < eps`, long relators, or both:
  * restate `PocketPinchStatement` and `PocketPinchLabelledStatement` in `OsinPocketPieces`;
  * pass the binder through `sectionPocketCutInput_of_pieces` and `sectionPocketCutInput_of_residuals`, and raise the thresholds in the two section theorems;
  * run one Rule 22 co-probe with the users listed in "The wrap refutation of the pinch". Nothing is staged before the ruling.

* Binder 5: not written here until kh-ejz or the lead confirms the handover. If this lane gets it, the producer takes audit-sec5's gap-only pocket, and configuration (b') stays with the pinch.
* kh-torsion's R1/R2 answer. Its report was last touched at a67ce2a65, and there has been no answer since the 15:00 follow-up.
  * Under R1: tell hull-select and kh-ejz that the carrier form is fixed.
  * Under R2: send jacobson the final `exists_twoCollars_of_ne_or` signature. Then run one Rule 22 co-probe over `OsinPocketPieces`, `OsinPocketRegionOfSimple`, `OsinPocketCollarOfGeodesic`, kh-torsion's `GeodesicCollarStatement`, hl-lemma46's lemma and its four users, and land everything in one call.
* No probe of this lane is running. All eleven lane files equal main.

## Scope 1: Dahmani–Guirardel–Osin Theorem 2.35, analytic half

`cor:regular-nonmf-algebra` cites DGO 2.35 for simplicity and uniqueness of the trace of `C*_r(Q)`.

The route chosen with the lead is route B:

* Abbott–Dahmani's property `P_naive` gives Powers' averaging estimate.
* The estimate gives both clauses.
* No classical C⋆-algebra theorem is used (not Powers, Akemann–Lee, or Breuillard–Kalantar–Kennedy–Ozawa).

Closed chain, all compiled (classical axioms only):

```
NaiveFreeProductProperty G                    Algebra/NaiveFreeProductProperty
  -> PingPongConjugateProperty G              Algebra/NaiveFreeProductPingPong
  -> ConjugateAveragingCriterion G            Analysis/PowersPingPongEstimate
  -> PowersAveragingEstimate G                Analysis/ConjugateAveragingCriterion
  -> simple C*_r(G) and unique tracial state  Analysis/PowersAveraging, PowersAveragingUniqueTrace
  -> DGOTheorem235Printed                     Manuscript/NonMF/DGO235FromNaiveFreeProduct
  -> SimpleUniqueTraceAtHypEmbedded           Manuscript/NonMF/SimpleUniqueTraceFromNaiveFreeProduct
```

Endpoints:

* `TorsionFreePrinted.dgoTheorem235Printed_of_naiveFreeProduct :
  NaiveFreeProductAtAcylindricallyHyperbolic → DGOTheorem235Printed`
* `TorsionFreePrinted.simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct :
  NaiveFreeProductAtAcylindricallyHyperbolic → SimpleUniqueTraceAtHypEmbedded`
  (through dgo-geometric's Osin `(AH₄) ⇒ (AH₁)`)

The one open Prop, `NaiveFreeProductAtAcylindricallyHyperbolic`, has dgo-geometric's closed producer.
So `dgoTheorem235Printed : DGOTheorem235Printed` is closed (`Manuscript/NonMF/DGOTheorem235Proof`, cebe6f695).

Also compiled:

* the rescued 09-09 reductions: `DGO235UniqueTraceFromAveraging`, `DGO235FromPowersProperty`, `DGO235PowersRoute`,
  `DGO235PrintedFromGeometry`, `PowersAveragingFromPartition`, `PowersAveragingFromPowersProperty`,
  `PowersAveragingSingleClass`, `PowersAveragingComposition`, `GroupHilbertSubsetProjection`;
* the corrected `DGOTheorem235Slice` header.

Landings: 100539f34, 460831be0, 04cc4aa44, 2a711b6bd, d748a8d40, 14914dfd2, 47c5d4b44, 0cdf0b924.

Census row: `metadata/nm-census-rows/dgo-analytic.tsv`.

* 09-13: `LINE:1728 formalized` on `dgoTheorem235Printed`.
* It supersedes the 09-11 row `LINE:1688 partial`, which was pending the P_naive producer.

## Scope 2 (helper H2 hull-assembly): Osin Appendix §9 assembly

* `GGT/VanKampen/Estimating/OsinAppendixAssembly.lean` (ce6930740):
  * `OsinSection97InputsStatement`, `osinLemma97Section_of_inputs`, `relativeGreendlingerQuasiGeodesicLeastArea_of_inputs`;
  * the two ρ-thresholds `exists_rho_widthBudget` and `exists_rho_muSqrt`.
* `GGT/VanKampen/Estimating/OsinAppendixAssemblyPocket.lean` (a956f3d3d), the descent of Lemma 9.7(b):
  * `RealizedSectionFamily.ExteriorLarge`, `ExteriorUniqueAt`, `exteriorSectionLength`;
  * the named input `OsinExteriorDoubleCut`;
  * the pocket estimate `OsinExteriorDoubleCut.lastSection_total_gt`;
  * the induction on `m(Π)`, `exists_of_exteriorDescent`.

### Two findings on Osin's proof of Lemma 9.7(b) (arXiv:math/0411039v3, pp. 34–35)

1. **Threshold slip** (correction approved).
   * `Π` minimises `m(Π)` among cells above `1 − 11μ`.
   * The new cell `Π′` is only shown above `1 − 13μ`, so it need not lie in the class.
   * The class is taken at `1 − 13μ`; it is nonempty by Corollary 9.6's `11μ` cell.
2. **The step needs clause (a) at the pocket.**
   * Osin's (40) at `1 − 11μ` rests on "Corollary 9.6 and the inductive assumption" at the pocket `Γ_1`: clause (a) `(∗)` plus Lemma 9.4 at a smaller diagram.
   * `OsinLemma97Below`, the inductive hypothesis that `DescentInput` receives, carries only clause (b).
   * Clause (b)'s `1 − 13μ` at the pocket gives only `1 − 15μ` towards `t_2`.
   * So the step producer must either receive clause (a) of the smaller diagrams, or carry the `11μ` cell of the pocket as an input. The induction in `OsinAppendixSectionInduction` already proves `(a) ∧ (b)`.

* `GGT/VanKampen/Estimating/OsinAppendixAssemblyDescent.lean`, design F2 (approved).
  * Commits 57ddccb86, dea18154c, 5f5dddd41; compiled in probe 0912-001046-51202.
  * `OsinDescentMergeInput` and `OsinDescentStepInput`: named producers quoting Osin; the step carries Corollary 9.6 at the pocket.
  * `exists_exteriorUniqueAt_of_merge_step` and `exists_sectionSelection_of_exteriorUniqueAt`.
  * `osinLemma97bConclusion_of_exteriorUniqueAt`: clause (b) in hull-select's shape, disjointness from compatibility, distinct regions from nondegenerate target arcs.
  * `descentInput_of_merge_step : OsinDescentMergeInput → OsinDescentStepInput → … → DescentInput`.
  * 09-13: `OsinDescentStepInput` retired (5957159598), see Finding 3.
* Repair 948130d79: after eb4bc56f4, the wired pocket module changed the signature of `contiguityDegree_lt_mu_of_o52`, and the root was red until this repair.

### Finding 3: route F2's step producer is circular; replaced by the pocket cut

* `OsinDescentStepInput` carries the `11μ` cell of Corollary 9.6 at the pocket.
* Producing it needs clause (a) of Lemma 9.7 at the smaller diagram, and `OsinLemma97Below` does not carry clause (a).
* So any producer of the step would have to run Lemma 9.7 itself.

The approved replacement (lead, 09-12):

* It keeps `OsinAppendixAssemblyDescent` unchanged.
* It runs Corollary 9.6 at each pocket directly from `OsinLemma97Below` and a fresh globally distinguished section system of the pocket.
* It uses strong induction on the pocket's `R`-cell count.
* No extremality transport is needed, and the only leaf is the planar cut.

* `GGT/VanKampen/Estimating/OsinAppendixDescentCut.lean` (4f3d38859, 08381ed21):
  * the leaf `OsinSectionPocketCut`, which extends `OsinExteriorDoubleCut` with `sectionTransport` to section `j` of `Δ` at part 3;
  * `SectionPocketCutInput`, `OsinLemma97Below.mono`, `OsinSectionPocketCut.false_of_inner`,
    `RealizedSectionFamily.emptyOfLeastArea`, `osinLemma97bConclusion_of_region`.
* `GGT/VanKampen/Estimating/OsinAppendixDescentInduction.lean` (f82dfe0c3, 08381ed21):
  * `exists_elevenCell_of_below`: Corollary 9.6 at a least-area diagram below the induction measure;
  * `OsinSectionPocketCut.exists_large_region`: the pocket induction, with conclusion `1 − 13μ` towards section `j`;
  * `descentInput_of_sectionPocketCut : … → SectionPocketCutInput → DescentInput`.
  * Both modules compiled in probe 0912-100628-69222 (base 08381ed21), classical axioms only.
* `GGT/VanKampen/Estimating/OsinAppendixLemma97Pocket.lean` (4b9f8144d, 42e5d2843; compiled in probe 0912-105301-92538, base 42e5d2843, classical axioms only):
  * `OsinSection97PocketInputsStatement`: cut producers, hull-euler's `PhiPrimeCountInput` through `eulerCountInput_of_phiPrimeCount`, and `SectionPocketCutInput`;
  * `osinSection97Inputs_of_pocketInputs`, `osinLemma97Section_of_pocketInputs`;
  * `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs`, with O52 given by `Embedded.o52LeastArea`.

Residual of G6 on this route: `SectionPocketCutInput` only.

* Since 09-13 it belongs to this lane and is assembled from the pieces above (`sectionPocketCutInput_of_pieces`).
* Its 09-12 attribution to hull-respell (`OsinAppendixPocketCutProducer`) is superseded. hull-respell now owns the piece `PocketPinchStatement`.
* The transports are go-lemma42's pieces.

Leaves of the Lemma 4.4 waist on this route (`relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs`):

* `OsinLemma94SectionStatement` (hull-unbound, hull-count94);
* `MultipleEdgeCutInput` and `LoopCutInput` (G2: hull-select, go-lemma42; `LoopCutInput` on hold 09-13);
* `PhiPrimeCountInput` (hull-euler);
* `SectionPocketCutInput` (dgo-analytic, from the pieces).

O52 is `Embedded.o52LeastArea`.

## Fleet traps found here

* `autoImplicit` is on: a missing import reads "Function expected … unknown
  identifier treated as implicitly bound".
* `push_neg` and `ContinuousLinearMap.add_apply` are deprecated at the pin.
* `set 𝔅 := <operator type>` shadowed an argument and broke rewrites.
* `congr 1` can close the goal, leaving the next tactic with "no goals".
* `positivity` on a `set` of a `Finset.card` timed out in `whnf`.
* `rw [a.2.source = i]` through `a.2.sourceArc.length / (cell Delta a.2.source)…`
  fails ("motive is not type correct"); rewrite a separate `have` about the cell
  length.
* `Monoid.CoprodI.of m` over `fun b ↦ ↥(S b)` infers the family as `Subtype`
  over `G → Prop`; state letters over an `abbrev` family.
* `simpa … using h` compares the final types at reducible transparency, so it
  fails when an implicit argument is a def projection (`(emptyOfLeastArea …).diagram`
  against `Y`); use `rw` then `exact`.
* `nmprobe.sh` refuses when a file listed in the lane's `.files` is missing
  locally; write the file before listing it.
