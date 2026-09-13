# dgo-geometric lane report

Lane of the non-MF verbatim swarm. It owns the geometric DGO/Osin carriers and the GHW archimedean
modules `Kazhdan/GHWArchimedeanMinkowski` and `Kazhdan/GHWArchimedeanWalls`.

## 2026-09-13: the wrap case of the pinch, model test

The lead's item: model the wrap case of the pinch, the one pinch residual with no planned proof.
In that case `K` follows the boundary and is pinched, and `t_1 = ∂Π` or `t_2` holds every dart of
`K` on `∂X`. Send the result to ghw-assembly, especially a refutation.

### Verdict: the four pinch Props fail at `ε = 0`

The four Props are false at the universes `0, 0, 0`. There is no ULift transport to other
universes.

- `PocketPinchStatement`, `OsinPocketPieces.lean:260`.
- `PocketPinchLabelledStatement`, `OsinPocketPieces.lean:272`.
- `PocketPinchPinchedStatement`, `OsinPocketPinchUnpinched.lean:61`, through
  `pocketPinchStatement_of_pinched`.
- `PocketPinchStepStatement`, `OsinPocketPinchStep.lean:60`, through
  `pocketPinchLabelledStatement_of_step`.

### The shape (`OsinPocketWrapRose`)

The counterexample is a three-petal rose with one vertex. Its darts are `0..5`, with
`alpha = (0 1)(2 3)(4 5)` and `sigma = (0 1 2 3 4 5)`. It has four faces:

- `κ = [0,2,4]`, an ordinary face reading `x⁻¹ · xy · y⁻¹`;
- `Π = [1]`, a relator cell reading `x`;
- the exterior face `[3]`;
- `R = [5]`, a relator cell reading `y`.

The pocket face set `wrapK` on `{κ, R}` has `ε = 0` and positions 0 and 1:

- source `Π` and kept cell `R`;
- empty sides, `t_1` = all of `∂Π`, `t_2` = all of `∂X`;
- boundary cycle `[0,2]`.

It is a closed walk, it follows the boundary, and it is pinched at the one vertex. So it is the
wrap residual with `t_1 = ∂Π` and `t_2 = ∂X` at the same time.

### Why no copy is simple (`OsinPocketWrapMonogon`)

`not_simple_of_monogons`: at `ε = 0`, if the source cell and the exterior face each have one
dart, no pocket face set is simple. The sides are empty and each arc has at most one dart.

- Both arcs empty: the cycle is empty, which is impossible.
- Exactly one arc empty: the cycle is the reversed dart of one monogon. By connectivity, every
  face is that monogon or lies in the face set, so the other monogon lies in the face set.
- Both arcs of one dart: the dart of `t_1` is a loop, so `t_2` starts at the vertex where `t_1`
  starts, and `vertex_nodup` fails.

An O-equivalence keeps the lengths of the relator words and the boundary word
(`no_simple_of_oEquivalent_monogons`).

### `ε ≥ 1` and the consumer

- At `ε ≥ 1` the rose is rescued on paper: `K' = {R}` with `s_1 = [5]` and empty arcs is simple
  on the rose itself. So the rose does not refute `ε ≥ 1`. `ε ≥ 1` is untested in general.
- `hpinch : PocketPinchLabelledStatement` of `sectionPocketCutInput_of_residuals`
  (`OsinPocketCutResiduals.lean:45`) is false as stated. There are two candidate repairs, both
  untested, and the lead decides:
  - a `0 < ε` binder. `OsinCCondition` does not supply it, since
    `osinCCondition_emptyFamilyModel` holds at every `ε`;
  - long relators, `IsSmallCancellation.long` with `2 ≤ ρ`. This kills the monogon family but
    does not decide `ε = 0`.

### Lean

- `OsinPocketWrapMonogon` and `OsinPocketWrapRose` are new and unwired, landed unverified at
  6dfa779fe. The endpoints are `PocketPinchWrapModel` and `PocketPinchWrapRefutation`.
- Probe 0913-161551-58985 was red on two tactic lines of Monogon. The fix landed at 87358b0ad.
- Probe 0913-163031-39703 is GREEN, with BUILT for both modules. Every `#audit_axioms` and
  `#audit_closed_axioms` line passes within `propext`, `Classical.choice` and `Quot.sound`.
- Sent: the full result to ghw-assembly, the shape to main, and notices to hull-respell, kh-cckw
  and dgo-analytic.

### Residual and next

- Get hull-respell's exact wrap shape and compare it with the rose.
- No wrap Lean until dgo-geometric, hull-respell and ghw-assembly agree on the split.
- Lower priority: dgo-analytic's collar re-test under `K.Nondegenerate`. Configuration A only if
  R1 wins. C3 and C5 are skipped.

## 2026-09-13: W1 PocketRegion piece Props, model and truth audit

The lead's item: audit the W1 PocketRegion piece Props as they land. For each Prop, find a
nonvacuous instance or refute it formally, as `RegionShellingSpurCounterexample` does. Put the
fixtures in new modules of this lane. audit-sec5 tests the LoopCut cap, so this lane skips it.

### Fixtures (all in `GGT/VanKampen/Estimating/`, unwired)

These are model tests. None of them certifies a printed sentence.

- `OsinPocketPinchedTwoGonModel` (4b78f0090, green) is a ten-dart map:
  - a relator cell `Π = [0,1,2]`;
  - two digons `a = [3,4]` and `b = [5,6]` that meet only at the vertex `{1,3,6,8}`;
  - the exterior face `[7,9,8]`.

  By `no_faceSetBoundary` and `no_contiguity`, the face set `{a, b}` has no
  `Embedded.FaceSetBoundary`, so it carries no `Embedded.Contiguity`.
- `OsinPocketPinchedTwoGonRegion` (26f3e086e, probe 0913-102131-19819 GREEN) builds
  `pocket : PocketRegion diagram` on `{a, b}`. Its cycle `[5,3,4,6]` does not follow the boundary
  (`not_followsBoundary`), and it is not a simple closed walk (`not_isSimpleClosedWalk`). So
  `PocketRegion` admits pinched pockets.
- `OsinPocketPinchedTwoGonDiscCollapse` (4894cfceb, probe 0913-111918-28699 GREEN) runs route A
  (`Surgery.InnerDiscRegion.ofPocketRegion` and `mergedGeometry`) on that pinched pocket:
  - it gets the disc region `R`;
  - it gets the decomposition hypothesis of `EmptyTwoGonInput`, with empty sides;
  - it gets a contiguity geometry `H` from `Π` to the exterior, with arcs of lengths 2 and 2.

  The endpoint is `PinchedPocketDiscCollapseModel`.
- `OsinPocketPinchedTwoGonLobe` (4181011af, probe 0913-132420-4350 GREEN) makes the digon `a`
  (reading `x⁻¹ x`) a second relator cell and builds two pocket face sets of that diagram, both
  between positions 0 and 2:
  - `pinchedK`, on `{a, b}`: source `Π`, kept `a`, empty sides, arcs `[0,1]` and `[4,6]`. It
    satisfies the hypothesis of `PocketPinchPinchedStatement` (`pinchedK_not_followsBoundary`,
    `pinchedK_not_unpinched`, `pinchedK_not_simple`).
  - `lobeK`, on `{a}`: the same source and kept cells, arcs `[0]` and `[4]`. It is simple
    (`lobeK_simple`).

  The endpoints are `pinchedPocketLobeModel` and `pinchedPocketLobe_conclusion`.

### Verdicts

1. hull-select, the zero-cell merge producer (the inputs of `false_of_collapse_singleton`): a
   producer that goes through the face-set boundary of the merged face set fails at a pinch
   (`no_faceSetBoundary`). The route A collapse does not fail there: `R`, `H` and the
   `EmptyTwoGonInput` decomposition exist on a pinched pocket. The model carries no section
   family, so it tests only these geometric inputs.
2. kh-torsion, `GeodesicCollarStatement`: I audited it and found no refutation. The strip
   construction goes through. fff-quotient's `SurgeryMonogonDoubling` handles the monogon side,
   where `FaceEdgeDoubling` needs a face of length > 1. There is no fixture.
3. dgo-analytic, `PocketPinchStatement` and `PocketPinchPinchedStatement`: the Props are nonvacuous
   and hold on the pinched model, for a cheap reason. The conclusion ties the simple pocket face
   set `K'` to `K` only through `D`, `ε`, `lo` and `hi`.
   - On a pinched pocket, a lobe in `X` itself witnesses the conclusion with the identity
     O-equivalence (`pinchedPocketLobe_conclusion`).
   - kh-cckw's "X itself cannot serve" holds for `K` itself, not for every `K'`. This matches
     hull-respell's lobe selection.
   - A consumer that needs `K'` to keep the faces, the arcs or the sides of `K` cannot get that
     from the Prop.
   - The hard pinch cases are Configuration A (notch) and Configuration B (lake). Both are modelled
     below, at the level of the noncrossing `Simple` prediction.
4. hull-euler, C3 to C5 of `PhiPrimeCountInput`: no truth question is left.
   - Proved: C3 (`exterior_of_isTwoGon`, hull-euler), C4 (`cornerTwoGonInput`, leavitt-units,
     90245333d), C5 (`cellFaceCountInput`, hs-vanishes, a6a2cadda) and C6
     (`emptyTwoGonInput_holds`, fff-periodic, 2aa17abb0).
   - C6′ (`TwoGonHoldsInput`) is the only stated input left. It needs a least-area diagram with a
     globally distinguished section family, so it is not modelled.

The baseline-debt LINE:1725 finding went to baseline-debt. The dgo-analytic stale-lines finding
is moot and was not sent.

### The noncrossing `Simple` prediction (R2)

dgo-analytic's R2 would make `PocketFaceSet.Simple` a noncrossing closed walk whose outer cycle
follows the boundary. dgo-analytic predicts two outcomes:
- Configuration A: the pocket sectors lie between the passages, so the inner cycle fails and the
  outer cycle follows.
- Configuration B (lake): the outer cycle fails.

`Estimating/OsinPocketPinchedTwoGonOuterFollows` tests Configuration A on the pinched two-gon model.
It landed at e533e5581. Probe 0913-134649-6539 is GREEN with `BUILT`, no warnings, and the file is
byte-equal to main. It uses kh-ejz's `isNoncrossingClosedWalk_pinchCycle`.
- `sideOutside_pinchCycle`: the outer side of `[5,3,4,6]` is the relator cell together with the
  exterior face.
- `pinchCycle_outerCycle_followsBoundary`: the outer cycle `[9,8,0,1]` follows the boundary.
  `9 ↦ 8` and `0 ↦ 1` are face steps, and `8 ↦ 7 ↦ 0` and `1 ↦ 2 ↦ 9` cross the internal edge
  `{2,7}`.
- `pocket_inner_not_follows_outer_follows`: the prediction holds on `pocket`.
- `pinchedPocketNoncrossingOuterFollowsModel`: `pinchedK` meets the pinch hypothesis and fails
  today's `Simple`, but it meets the proposed `Simple`. So under R2 this pocket needs no pinch.

Verdict for Configuration A: the prediction holds on this model.

`Estimating/OsinPocketLakeModel` tests Configuration B on the smallest map with that shape. It
landed at 67e5b2f9c, together with `pinchCycle_innerCycle_not_followsBoundary` in OuterFollows.
Probe 0913-140543-86239 (base 037386a74) is GREEN with `BUILT` for both modules, and both files are
byte-equal to main. The map is a rose with two petals:
- four darts, the edges `{0,1}` and `{2,3}`, and one vertex with rotation `0 ↦ 1 ↦ 2 ↦ 3`;
- the faces `K = [0,2]`, the lake `Π = [1]` and the outside `O = [3]`, so χ = 1 − 2 + 3 = 2.

At the vertex the sectors of `K` lie inside the passages, and `Π` and `O` are separated.
- `isNoncrossingClosedWalk_lakeCycle` and `lakeCycle_not_isSimpleClosedWalk`: the walk `[0,2]` is
  a noncrossing closed walk but not a simple one.
- `lakeCycle_innerCycle_followsBoundary`: the inner cycle follows, since `0 ↦ 2` and `2 ↦ 0` are
  face steps.
- `lakeCycle_outerCycle_not_followsBoundary`: the outer cycle `[3,1]` does not follow. The face
  step from `3` returns to `3`, and `3` is not internal to `{Π, O}` because its reversal `2` lies
  in `K`.
- `noncrossingPinchSidesPrediction`: both halves at once. It gives a planar map with a
  non-simple noncrossing closed walk whose inner cycle fails and outer cycle follows (the pinched
  two-gon), and another whose inner cycle follows and outer cycle fails (the rose).

Verdict for Configuration B: the prediction holds on this model. Under R2 the lake stays in the
pinch Prop. The model is a bare map: it has no labels, relator cells or arcs, so it is not a
`PocketFaceSet`.

### Model test of dgo-analytic's noncrossing region builder

dgo-analytic's `PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler`
(`Estimating/OsinPocketRegionNoncrossingWalk`, 8bbf0a9c8, green record 0913-140151-74557) builds
the pocket region on the walk's side. `Estimating/OsinPocketPinchedTwoGonNoncrossingRegion`
(80df00345, probe 0913-141525-34391 GREEN, byte-equal to origin) tests it on the pinched pocket
cycle `[5,3,4,6]`:
- `hw` is kh-ejz's `isNoncrossingClosedWalk_pinchCycle`, and `hfollows` is
  `pinchCycle_outerCycle_followsBoundary`;
- `hout` is `outerFace_not_mem_sideFaces_pinchCycle`;
- `heuler` is `pinchCycle_reclosed_euler`. It is `innerMap_euler` carried along
  `sideFaces_pinchCycle` by `reclosedMap_euler_congr`, which says the Euler characteristic of a
  reclosed map depends only on the face set and the listed cycle.

`pinchedPocketNoncrossingRegionModel`: the four hypotheses hold together, and the region built has
an inner cycle that neither follows its boundary nor is a simple closed walk.

Verdict: the builder is nonvacuous on a Configuration A pocket, whose cycle is not simple, so
`PocketRegion.ofSimpleClosedWalk` cannot apply. On the rose `hfollows` fails
(`lakeCycle_outerCycle_not_followsBoundary`), so the builder does not reach a lake.

### Residual and next

No Prop owned by this lane is open. These are green as landed, so none needs a second landing:
`OsinPocketPinchedTwoGonLobe` (4181011af), OuterFollows and `OsinPocketLakeModel` (67e5b2f9c),
and `OsinPocketPinchedTwoGonNoncrossingRegion` (80df00345). Next, in order:
1. hull-respell's smallest A and B, as dgo-analytic asks, once their dart lists are available;
2. if the lead asks, a diagram-level lake fixture: a `PocketFaceSet` with the source cell in the
   lake.

## 2026-09-13: P_naive wiring check

The lead's item: the census lists `NonMF.NaiveFreeProductPropertyOfAcylindricallyHyperbolic` as an
unwired carrier of a partial row, and dgo-analytic's report names this lane as the owner of the Prop.
If it has a green record, queue it; if the Prop is not closed, say what is missing.

Checked on origin/main after 22108b3e3, with the census files at 39dd43b39.

### Wiring: done, no new queue line

- `Manuscript/NonMF/NaiveFreeProductPropertyOfAcylindricallyHyperbolic` (baseline-debt) was landed in
  95e6d09ca, the only commit that touches it. It is root-imported at `GroupApproximation.lean:4875`.
- It entered the root in wave 3: `rw-wave3.mods` line 15, ROOT GREEN 0913-034741-17099, LANDED ROOT
  ce699b9b8.
- Its wire-queue line already exists (line 374, baseline-debt 296386753). Its md5 `ca000340` equals the
  one in baseline-debt's green records 0913-020324-57087, 0913-021321-7359, 0913-022427-58586,
  0913-025420-71482 and 0913-034738-16893.
- Census merges 0913-025455, 0913-032518 and 0913-034415 all ran at bases before ce699b9b8. They gave
  row `92115dd7edef`@1725 the reason "carrier not root-reachable" for this module.
- Merge 0913-042746 (base 395b3c31c, landed 39dd43b39) gives no such reason. Every declaration of the
  row is defined, compiled and root-reachable there.

### The Prop is closed

- `TorsionFreePrinted.NaiveFreeProductAtAcylindricallyHyperbolic : Prop` states that every countable
  `G` with `IsAcylindricallyHyperbolic G` and `HasTrivialFiniteRadical G` has
  `NaiveFreeProductProperty G`.
- `naiveFreeProductAtAcylindricallyHyperbolic` proves it
  (`Manuscript/NonMF/NaiveFreeProductAtAcylindricallyHyperbolicProof`, root-imported,
  `#audit_closed_axioms`).
- The proof unpacks `GGT.PNaive.naiveFreeProduct_of_isAcylindricallyHyperbolic` (`GGT/PNaiveAcylindrical`,
  root-imported, `#audit_axioms`). Its only hypotheses are the class and `hrad`.
- `IsAcylindricallyHyperbolic` is the definition, not a cited result: some alphabet has a hyperbolic
  Cayley graph, with an acylindrical, non-elementary action.
- All eight P_naive modules in this lane's `.files` are root-imported, and their bytes match origin.
- Nothing is missing.

### What keeps row `92115dd7edef` partial

- `census/merge_rows.py` grades a union row partial when any of its lane rows is partial.
- There are three `LINE:1725` rows: baseline-debt `partial`, cite-osin `formalized` and sec5-sentences
  `formalized`.
- baseline-debt's row describes the DGO 2.35 half, which is tex line 1728, row `f2bf6328169e`
  (formalized).
- The fix belongs to baseline-debt: re-grade its `LINE:1725` row, or move it to the line-1728 sentence.
- dgo-analytic's report, lines 33-34, still lists `NaiveFreeProductAtAcylindricallyHyperbolic` as the
  residual Prop, owned by dgo-geometric. That line is stale.

## 2026-09-13: W3 MirrorFold leaf truth audit

The lead's assignment:
- check that `Systolic.MirrorFoldDistinctStatement X` and `Systolic.MirrorFoldPinchedStatement X`
  (`GGT/SystolicDiscMirrorFoldCases`, 0fb6f2305) hold for every triangle complex `X`;
- build models;
- check the consumer.

Checked against origin 19461b5bc.

### Verdict: both Props are true for every `X`
- The proof uses only irreflexivity of `X.G` and `tri_adj`.
  - Write the face of `d` as `[d, d1, d2]` (vertices `u → v → w`) and the face of `alpha d` as
    `[alpha d, e1, e2]` (`v → u → w'`).
  - Adjacent labels make `u, v, w` pairwise distinct disc vertices, and likewise `u, v, w'`.
  - No edge joins `w` and `w'`.
- No systolic, 6-large, simply connected or locally finite hypothesis enters.
- `TriangulatedDisc` asks for no simplicity, no injective labels and no simple boundary.

**Distinct (`w ≠ w'`).**
- The fold:
  - delete the six triangle darts;
  - pair `alpha d2 ↔ alpha e1` and `alpha d1 ↔ alpha e2`;
  - keep `facePerm` on the remaining darts.
- Counts: the rotations at `u` and `v` stay single cycles, and those at `w` and `w'` merge. So V−1,
  E−3, F−2, the map stays connected, and χ = 2.
- The outer cycle and `base` are unchanged, so `γ` is kept and `innerFaceCount` drops by exactly 2.
- In repo primitives:
  1. `EdgeDeletion` of `d`;
  2. `FoldMap.IsFoldable (p := d1) (d := d2) (e := e1)`, whose `distinct_ends` is exactly `w ≠ w'`;
  3. `FoldStage.deleteDigon`.

**Pinched (`w = w'`).**
- Delete the edge of `d`. The face `[d1, d2, e1, e2]` passes through `w` twice.
- Split `w` with `FoldMap.joined M d1 e1`, which is `PinchLemma` with `(p, d, e) := (d1, d2, e1)`:
  - `split_euler` gives χ = 4;
  - `reach_or_reach` and `not_reach_p` give exactly two components, with faces `[d1, e2]` and
    `[d2, e1]`;
  - `CombMap.restrict_planar_of_euler_four` makes both planar.
- Keep the component with the outer face and delete its digon. The drop is at least 2 and `γ` is
  kept. The loss can exceed 2, which is why the Prop says `+ 2 ≤`.
- Coinciding edges:
  - a coinciding `u–w` edge (`e1 = alpha d2`) or `v–w` edge needs no special case, because the spur
    side is a one-edge sphere that cannot contain the outer face;
  - both coinciding is impossible, because the pair would close up with no outer face.
- `eulerCharacteristic_le_two` is proved in `VanKampen/CombMapEulerUpperBound`.

### Models (paper, dart level)
`X` is the 2-simplex on `{a, b, c}`, with `x̄ = alpha x` and `sigma = facePerm ∘ alpha`.

1. **Distinct.** `u=a, v=b, w=c, w'=c`.
   - Darts: `d:u→v, p:v→w, q:w→u, r:u→w', s:w'→v` and their reverses.
   - Faces: `[d,p,q]`, `[d̄,r,s]`, outer `[q̄,p̄,s̄,r̄]`. V=4, E=5, F=3, and `γ = [a,c,b,c,a]`.
   - D' is the path `a–c–b` (V=3, E=2, F=1). `innerFaceCount` goes 2 → 0.
2. **Pinched, shared `u–w` edge.**
   - Darts: `d:u→v, p:v→w, q:w→u, s:w→v` and their reverses.
   - Faces: `[d,p,q]`, `[d̄,q̄,s]`, outer `[s̄,p̄]`. V=3, E=4, F=3, and `γ = [b,c,b]`.
   - D' is the single edge `b–c`. `innerFaceCount` goes 2 → 0.
3. **Pinched, two lobes.** Add `x=a`.
   - Darts: `d,p,q`, `d̄, r:u→w, s:w→v`, `t:v→x, m:w→x`, and their reverses (14 in all).
   - Faces: `[d,p,q]`, `[d̄,r,s]`, outer `[q̄,r̄]`, `[p̄,t,m̄]`, `[s̄,m,t̄]`. V=4, E=7, F=5, and
     `γ = [a,c,a]`.
   - The split leaves the outer edge `a–c` and a separate lobe with χ = 2. `innerFaceCount` goes 4 → 0.

### Consumer
- `CCKW.systolicInvariantClique_of_zipFold` takes `∀ (V : Type) (X), MirrorFoldStatement X`.
  - It uses it only at its own `X`, through `exists_invariantClique_of_linksSixLarge`.
  - That lemma passes it to the projection-clique, triangle-condition and no-induced-4/5-cycle lemmas.
- `mirrorFoldStatement_of_cases` splits on `third d = third (alpha d)`. It hands the two Props the
  same `X` and nothing else.
- `hzip` is closed: `zipSpurStatement` in `GGT/SystolicDiscZip`.
- Universes: the Props live at `V : Type u` with `map : CombMap.{0}`, and every construction above is
  a subtype of `Dart`.
- Once both leaves close: `hfold := fun V X => mirrorFoldStatement_of_cases X (distinct X) (pinched X)`.

### Sent, residual and next
- Sent to main and to the owners, fff-periodic and systolic-counts (Pinched) and ko-closed and
  kh-cckw (Distinct).
- Residual Props owned by this lane: none.

### Lean nonvacuity fixture
- `GroupApproximation/GGT/SystolicDiscMirrorFoldModel.lean` (580 lines, unwired) landed at
  bb5b595bb.
  - Probe `0913-042330-95256` on base bb5b595bb: PROBE GREEN, with BUILT
    `GroupApproximation.GGT.SystolicDiscMirrorFoldModel` and no errors.
  - Both `#audit_closed_axioms` checks pass.
- `X = MirrorFoldModel.simplex`, the 2-simplex on `Fin 3`: `G := ⊤`, and `Tri` holds for
  pairwise distinct triples.
- Discs:
  - `Distinct.disc` (model 1, 10 darts), with `DistinctFold.disc` (the path, 4 darts);
  - `Pinched.disc` (model 2, 8 darts), with `PinchedFold.disc` (the edge, 2 darts).
- Orbits are classified with `OrbitClassifier.orbitEquiv`, as in `VanKampen/SelfContiguityModel`.
  Every finite check is `decide`.
- Endpoints: `mirrorFoldDistinct_nonvacuous` and `mirrorFoldPinched_nonvacuous`. Both are closed
  `∃` statements, checked with `#audit_closed_axioms`.
  - Each exhibits a disc `D` and a dart satisfying every premise of its case.
  - It also gives a disc `D'` with the same boundary and `D'.innerFaceCount + 2 ≤ D.innerFaceCount`.
- The fixture certifies no manuscript step and proves neither Prop.

## 2026-09-13: GHW char 0 handed to ghw-assembly; archimedean half on main

This lane's section of ROSTER-0913 says: "Target: closed GHWCharZeroFiniteness. Also: GHWArchimedeanBound and
GHWArchimedeanSeparation green; land the in-flight files." A reassignment line in the same roster
moves GHW char 0 (`Kazhdan/GHWCharZero`, `Algebra/IntegerGridFinite`) to ghw-assembly, so this lane
has stopped its char-0 modules.

### Char 0: stopped, with one duplicate on main
- `Algebra/IntegerPolynomialUnisolvence` was landed unverified at 4896458dc and is not wired. It
  proves the same two facts as ghw-assembly's `Algebra/IntegerGridFinite` (3108f1cc7, build fix
  489b5e67a):
  - integer polynomials of bounded total degree with bounded values on an injective complex grid
    form a finite set;
  - there is an algebraically independent `ℕ → ℂ` over `ℤ`.
- Its only probe, 0913-022920-78224, is red at line 122, and the audit of
  `finite_bounded_on_grid` shows `sorryAx`.
  - Cause: in `(coeff (expVec m) G : ℂ)`, `coeff` elaborates at `ℂ`.
  - Fix: `((coeff (expVec m) G : ℤ) : ℂ)`.
- The module is off this lane's probe list. The lead decides whether it stays on main as an orphan.
- No files were written for the rest of the char-0 route. The design was: places over
  `ℤ[t_1..t_d]` for `p ∣ M` and for total degree, archimedean places over grid evaluations, then
  `GHW.hasHaagerupProperty_of_countable_places`. It matches ghw-assembly's report.

### Archimedean half
- `GHWArchimedeanBound`, `GHWArchimedeanSeparation` and `GHWArchimedeanWedge`:
  - their origin/main blobs equal 6d8971521, 448d1bf45 and 4197466c8, and all three are wired in
    the root import list;
  - sec2-sentences' probe 0912-093859-21657 built Separation;
  - probe 0912-094259-57545 was green for Bound, where `separationFinite` and
    `ghwArchimedeanAffineBound` pass `#audit_closed_axioms`;
  - re-verification probe 0913-025429-71955 (base c3cfee844) is PROBE GREEN. Both modules were
    replayed from cache (inputs unchanged, 0 rebuilt), and Minkowski, Walls and Interfaces are
    recorded COMPILED.
- `GHWArchimedeanMinkowski` and `GHWArchimedeanWalls`: origin/main equals the green landings
  b5e5abc13 and 896416980, and both are wired.

### In-flight files
- All 28 files on this lane's probe list are byte-identical to origin/main (`git hash-object`
  against the origin blob).
- 26 are imported by the root. `GGT/HypEmbeddedCentralizer` and `GGT/OsinLinealAxis` are imported
  by the wired `Manuscript/NonMF/FreeNormalSubgroupSlice` and `GGT/OsinLinealExclusion`.
- Nothing is left to land.

### Residual Props and next item
- None owned by this lane. `GHWFinitelyGeneratedCharZero` belongs to ghw-assembly.
- Next: the lead's next item.

## 2026-09-12: GHW Theorem 4, archimedean half, wall modules green

### `GroupApproximation.Kazhdan.GHWArchimedeanMinkowski`
Compiled in probes 0912-004642-27086, 0912-092049-2822 and 0912-092424-41024. Landed at b5e5abc13;
re-landed normally after 0912-092424-41024.

- Minkowski space is `Fin 4 → ℝ` through `herm`/`coords`, with `lorentzQ v = v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2`
  and polar form `lorentzB v w = v ⬝ᵥ (gram *ᵥ w)`.
- `det_gram_ne_zero : gram.det ≠ 0` (explicit `gramInv`) replaces the earlier `det_gram`.
- `conjAct g : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)` is the determinant-normalized conjugation action of
  `GL (Fin 2) ℂ`, with `conjAct_mul`, `conjAct_one`, `conjAct_inv_conjAct`, `conjAct_conjAct_inv`,
  `lorentzB_conjAct`, `abs_det_conjAct`, `measurePreserving_conjAct`,
  `conjAct_origin_of_mem_unitary` and `measurePreserving_conjAct_shell`.
- `origin = ![1, 1, 0, 0]`, `shell = {v | 1 ≤ -lorentzQ v ∧ -lorentzQ v ≤ 2}`,
  `shellMeasure = volume.restrict shell`.

### `GroupApproximation.Kazhdan.GHWArchimedeanWalls`
Green probe 0912-092424-41024 (base 896416980). Repairs were landed unverified as b9f144093, 587dde0d5
and 896416980: `open scoped symmDiff`, and a classical indicator unfolding in the norm identity. The
module was then landed normally.

- `theorem conjAct_preimage_halfSpace (g : GL (Fin 2) ℂ) (x : Fin 4 → ℝ) :
  conjAct g ⁻¹' halfSpace (conjAct g x) = halfSpace x`
- `def koopman : GL (Fin 2) ℂ →* (Lp ℝ 2 shellMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 shellMeasure)`
- `def SeparationFinite : Prop := ∀ g : GL (Fin 2) ℂ,
  shellMeasure (halfSpace (conjAct g origin) \ halfSpace origin) ≠ ⊤ ∧
  shellMeasure (halfSpace origin \ halfSpace (conjAct g origin)) ≠ ⊤`
- `theorem isCocycle_wallCocycle (hfin : SeparationFinite) :
  Delorme.IsCocycle koopman (wallCocycle hfin)`
- `theorem norm_wallCocycle_sq (hfin : SeparationFinite) (g : GL (Fin 2) ℂ) :
  ‖wallCocycle hfin g‖ ^ 2 = (shellMeasure (halfSpace origin ∆ halfSpace (conjAct g origin))).toReal`
- `def wallAction (hfin : SeparationFinite) (c : ℝ) : Haagerup.AffineAction.{0, 0} (GL (Fin 2) ℂ)`
  with `wallAction_b : (wallAction hfin c).b g = c • wallCocycle hfin g`
- `def Haagerup.AffineAction.comapHom (A : AffineAction G) (ρ : Γ →* G) : AffineAction Γ` with
  `comapHom_b`.

Every audit closure is `[propext, Classical.choice, Quot.sound]`.

### Residual (with sec2-sentences)
`SeparationFinite` is a hypothesis in Walls only. sec2-sentences discharges it in
`Kazhdan/GHWArchimedeanBound` (`separationFinite`, from `Wedge.separation_diff_lt_top`). The same
module proves `ghwArchimedeanAffineBound : GHWArchimedeanAffineBound`. When this section was
written, neither `Kazhdan/GHWArchimedeanSeparation` nor `Kazhdan/GHWArchimedeanBound` had compiled.
Both compiled later on 09-12 (see the 2026-09-13 section). Pre-probe fixes sent to sec2-sentences:

- `open scoped symmDiff` in Bound;
- drop the unused `with hg`;
- `push_neg` → `push Not` in Separation.

No census row: these modules are infrastructure for the Toeplitz–Jacobson remark (tex line 1146,
[GHW, Theorem 4]) and certify no printed sentence on their own.

### Earlier compiled landings of this lane
- `GHWInterfaces`: `GHWArchimedeanAffineBound`, `GHWComplexEmbeddingExtension`.
- `ghwComplexEmbeddingExtension` (c577ea5ec).
- `isAcylindricallyHyperbolicOsin_of_limitSet`, `isAcylindricallyHyperbolicLimitSet_iff_all` (6b5a5f75e).
- `dgoTheorem235Printed` (cebe6f695).
