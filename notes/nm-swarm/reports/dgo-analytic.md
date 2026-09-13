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

### The pieces, in the order of the assembly

| Prop | Owner | Shape |
|---|---|---|
| `SectionPocketFaceSetInput`, `OsinSectionPocketFaceSetSectionStatement` | kh-ejz (kept cell through hull-select's zero-cell merge, copy through hs-vanishes' spur thickening) | two distinct exterior regions to section `j` give a `PocketFaceSet` in walk order (`ClosedWalk`) of an O-equivalent copy of the optimal diagram whose labels are letters of `symmetricLabelAlphabet D` |
| `PocketPinchLabelledStatement`, implied by `PocketPinchStatement` | hull-respell | a `PocketFaceSet` in walk order (`ClosedWalk`) of a diagram with legal labels has an O-equivalent copy with a `Simple` one (boundary cycle `IsSimpleClosedWalk`), by simple circuits or a 0-refinement |
| `PocketRegionOfSimpleStatement` | dgo-analytic | a `Simple` face set gives a `PocketCarrier` (both cycles `FollowsBoundary`, sides of length and norm at most `ε`) |
| `PocketCollarStatement` | dgo-analytic from kh-torsion's `GeodesicCollarStatement` | a `Nondegenerate` `PocketCarrier` has an O-equivalent copy with a `Collared` carrier (sides admissible geodesic words) |
| `PocketCellTransportStatement`, `PocketOuterTransportStatement` | go-lemma42 | regions of copies of the pocket to `t_1` and `t_2` glue back, target `OsinMultipleEdgeCut.ofPocketRegion` |

Assembly, proved:

* `PocketCarrier.nondegenerate_of_leastArea`: a carrier in a least-area diagram is nondegenerate.
* `PocketCarrier.nonempty_osinSectionPocketCut`: a collared carrier gives the cut.
* `sectionPocketCutInput_of_pieces hpinch hregion hcollar hcell houter`.
* `osinSectionPocketCutSection_of_pieces`.

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

### Residual Props of `DescentInput` on this route

* `OsinSectionPocketFaceSetSectionStatement` (kh-ejz).
* `PocketPinchLabelledStatement` (hull-respell), or `PocketPinchStatement` through the weakening lemma. kh-cckw reduced the unlabelled one to `PocketPinchPinchedStatement` (33951a5b6). Configurations A and B are escalated.
* `GeodesicCollarStatement` (kh-torsion, `SurgeryGeodesicCollar.lean:67`), in place of `PocketCollarStatement`.
* `PocketCellTransportStatement` and `PocketOuterTransportStatement` (go-lemma42).
* Outside `SectionPocketCutInput`, `descentInput_of_sectionPocketCut` still takes `LoopCutInput` (ruling (A) final), `MultipleEdgeCutInput`, `EulerCountInput`, `UnboundInput` and `O52LeastAreaStatement`.

Closed here:

* `PocketRegionOfSimpleStatement` (`pocketRegionOfSimple`).
* The nondegeneracy of carriers at least area (`nondegenerate_of_leastArea`).
* `PocketCollarStatement` from `GeodesicCollarStatement` (`pocketCollarStatement_of_geodesicCollar`, through hl-lemma46's two collars).

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
