# hull-component lane report

## Scope
Wall hbridge: `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}` from
`QuotientPeripheralLetterPullbackStatement` (GGT/HullSCLemma51EmbeddedProducer). hull-bridge integrates.
This lane owns (D), the letter pullback induction of Osin's Lemma 5.1, and the cut move outcome.

## Compiled on main (no hypotheses beyond the stated binders; `#audit_axioms` in each file)
- GGT/HullSCLemma51LetterPullbackAtoms: atoms, lifts of quotient relative balls, bounded products of images.
- GGT/HullSCLemma51LetterPullbackClose: `PullbackOutcome`, `mem_image_of_pullbackOutcome`.
- GGT/HullSCLemma51LetterPullbackRotate: `RotatedLift`, `exists_rotatedLift`.
- GGT/HullSCLemma51LetterPullbackInduction: `LetterStepBound`, `.or`,
  `quotientPeripheralLetterPullbackAt_of_letterStepBound`.
- GGT/HullSCLemma51LetterPullbackShortcutArcs, GGT/HullSCLemma51LetterPullbackShortcut: the M1 move
  `letterStepBound_of_not_isRelGeodesic : LetterStepBound D W q hq (fun w => ¬ ∀ r, IsRelGeodesic D (w.rotate r))`.
- GGT/HullSCLemma51LetterPullbackCutFaces (74c6b03ff), CutSides (14850636f), CutBlocks (4d91f2870): the face,
  side and block lemmas of the certificate cut.
- GGT/HullSCLemma51LetterPullbackCutOutcome (a1f2e52da): `CutMove`, its quotient facts,
  `CutMove.outcome_before` (the unknown letter after the arc) and `CutMove.mem_image_of_inner` (a bounded value).
- GGT/HullSCLemma51LetterPullbackCutOutcomeSides (27f56e14b): `CutMove.outcome_left`, a left side letter at the
  coset of the unknown letter becomes designated.
- GGT/HullSCLemma51LetterPullbackCutOutcomeRight (47b7225af): `CutMove.outcome_right`, and
  `CutMove.outcome : PullbackOutcome D q hq lam (pullbackAtoms W D lam r) N h n` for every cut move with
  `1 ≤ r`, `|L| + |arc| + |R| + |ext| ≤ r`, `r + 1 ≤ N`, `|arc| + |tail| ≤ n + 2`.
- Probes, all GREEN:
  - 0913-010957-99348 (Atoms, Close, Rotate, Induction, RelativeCosetPieces);
  - 0913-012328-36694 (ShortcutArcs, Shortcut);
  - 0913-034626-13821 (CutBlocks, with CutSides and CutFaces);
  - 0913-041859-87013 (CutOutcome);
  - 0913-044512-41174 (CutOutcomeSides);
  - 0913-045018-55444 (CutOutcomeRight).
- All of these are in the wire queue.

## Residual Props
None owned by this lane. The remaining assembly belongs to peers:
- M2, `letterStepBound_of_cutLiftOutcome`, is landed by debt-conditional (GGT/HullSCLemma51LetterPullbackCut,
  457c543a8, GREEN 0913-044157-34176). Its only non-input hypothesis is `CutLiftOutcome W D q hq`
  (GGT/HullSCLemma51LetterPullbackCutLift, hull-bridge).
- hull-bridge's GGT/HullSCLemma51LetterPullbackHolds was on disk and unlanded as of 09-13 05:05. It proves
  `CutLift.toCutMove`, `cutLiftOutcome` through `CutMove.outcome`, and
  `quotientPeripheralLetterPullbackStatement_holds : QuotientPeripheralLetterPullbackStatement.{u, v, w}`.
  The producer closes when that module lands and probes green.

## Case split of `CutMove.outcome` (as built)
The rotated lift `arc ++ tail = x ++ comp λ h⁻¹ :: y` either has the unknown letter after the arc, or
`arc = x ++ comp λ h⁻¹ :: y₁`.
- After the arc: `outcome_before`. The letter stays designated, and the new word is
  `respellInv L ++ respellInv rem ++ respellInv R ++ tail`.
- Inside the arc, with a left side letter `L[j]` at the coset of the unknown letter: `outcome_left`.
- Inside the arc, with a right side letter `R[j]` at that coset: `outcome_right`.
- Inside the arc, with no side letter at that coset: `mem_image_of_inner`. The face bounds `h`, which gives
  `q h ∈ q '' boundedProducts`.

## W1 (09-13 after the 08:30 restart): helper to dgo-analytic on the region piece
The lead assigned the uncollared pocket carrier with both FollowsBoundary over
`PocketRegion.ofSimpleClosedWalk` (a11a8d850). dgo-analytic handed this lane one sub-piece.
- GGT/VanKampen/SimpleClosedWalkSideFaces (d20913c51; GREEN 0913-090043-59913; in the wire queue):
  `SimpleClosedWalkSides.sideFaces_boundaryCycle_eq (hM : M.IsConnected) (boundary : BoundaryCycle M faces)
  (hf : f ∉ faces) : sideFaces M boundary.cycle = faces`, with `sideFaces_boundaryCycle_subset` (no
  connectivity) and the transport lemmas `faceOf_mem_iff_of_faceClass` and `faceOf_of_alpha_closed`.
- Consumer: dgo-analytic's Estimating/OsinPocketRegionOfSimple, for `PocketRegionOfSimpleStatement`. The kept cell
  and the source cell transfer from `PocketFaceSet.faces` to `(ofSimpleClosedWalk ..).faces` through this equality.
  The exterior face gives `hf`, and `CombMap.connected_of_planar` gives `hM`.
- Consumed: `pocketRegionOfSimple` (Estimating/OsinPocketRegionOfSimple) landed in c03054996 and closes
  `PocketRegionOfSimpleStatement`, with closed axioms [propext, Classical.choice, Quot.sound]. It built green
  together with this module in dgo-analytic probe 0913-090829-84396.
- dgo-analytic has no further sub-piece for this lane.

## Respelling lemma (09-13): helper to hull-unbound on the Lemma 9.4 cutting chains
The lead assigned the word-metric respelling lemma inside hull-unbound's split of
`OsinLemma94PolygonRealizationInput`. The earlier item, `SeparatingPathRemovalInput`, was stood off because
hull-unbound had started it; hull-unbound proved it at 7d4a2515f.
- GGT/VanKampen/Estimating/OsinLemma94WordRespelling (6b5a1f7d1; GREEN 0913-101505-99170; in the wire queue; the lead
  approved the word form):
  `exists_shorter_respelling_of_not_isLambdaCQuasiGeodesicWord`, with the binders of hull-unbound's
  `QuasiGeodesicRespellInput` (Estimating/OsinLemma94PolygonRealization). Take a violating subword with n letters
  and value g, so |g| + 2 < n. If g ≠ 1, a geodesic spelling is shorter. If g = 1, then n ≥ 3, and without its last
  letter the subword is spelled by the inverse of that letter.
- Consumer: hull-unbound's `OsinLemma94CuttingChainsInput`, with `ChainRespellInput` and `PendantPathRemovalInput`.

## Gap-length lemma (09-13): helper to hull-count94 on Stage B of the Lemma 9.4 side budget
The lead assigned one sub-piece of Stage B, and hull-count94 picked the gap-length lemma (roster l.740).
- GGT/VanKampen/Estimating/QuasiGeodesicValueOneGap (a3169d05f; GREEN 0913-134955-22334; in the wire queue):
  `IsLambdaCQuasiGeodesicWord.length_le_of_listVal_eq_one (h : IsLambdaCQuasiGeodesicWord D lambda c w)
  (him : i + m ≤ w.length) (hval : listVal ((w.drop i).take m) = 1) : lambda * m ≤ c`, and
  `IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one (h) (hlambda : 0 < lambda) (him) (hval) : m ≤ ⌈c / lambda⌉₊`.
  Vertices i and i + m coincide, so the quasi-geodesic inequality at (i, i + m) reads λm − c ≤ 0.
- Consumer: hull-count94's Estimating/OsinLemma94PolygonClasses. It counts the gaps at class ends against
  L = 24ε + 2(K+24)⌈(c+2)/λ⌉. fff-periodic's unlanded `stretch_le_length` covers this as its `alt = []` case,
  but this module does not import it.
- GGT/VanKampen/Estimating/OsinLemma94BudgetFilter (e48f35d1e; GREEN 0913-134955-22334; in the wire queue; candidate (a), the
  reindexing lemma): `classWordLength_eq_zero_of_forall_not_mem` and
  `OsinLemma94DensePolygonsAntiparallel.exists_of_budget_on`. The metric half applies with the side budget summed
  over any set of polygons that contains every polygon with an (A1) side.
- Consumer: hull-count94's Estimating/OsinLemma94PolygonClasses imports it and uses `exists_of_budget_on`.

## Class cover (09-13): helper to hull-count94 on `ClassCovers`
hull-count94 asked for the bubble accounting behind `Q.ClassCovers (24ε + 2(K+24)⌈(c+2)/λ⌉₊)` as a lemma over any
Q, with the Q-level facts as hypotheses. The hypothesis list went to hull-count94 before the probe.
- GGT/VanKampen/Estimating/OsinLemma94ClassCovers (GREEN 0913-150746-83718; landed with this report; in the wire
  queue):
  `OsinLemma94ClassPolygons.classCovers_of_endLoops : Q.ClassCovers (24 * eps + 2 * (K + 24) * B + T)`.
  Its hypotheses:
  - `hvalue`, `hcells`, `hcard`, and the class budget `Q.ClassBudget K`;
  - `hsameCell`: at most `T n` unbound darts have their own cell across;
  - `hside`: every other unbound dart facing no selected region lies across an (A1) side;
  - `hbubble`: on a one-class polygon the reverse dart lies in an (A1) class of a polygon with at least two
    classes, or in an end loop (`classEnd k i b` for budget classes, `regionEnd a t` for selected regions);
  - `hclassEnd`, `hregionEnd`: end loops have at most `B` darts.
- The count: region-facing darts `2ε|M| ≤ 24εn`; own-cell darts `T n`; the rest inject by reversal into the
  (A1) class darts, `2Kn` class-end loops and `4|M| ≤ 48n` region-end loops.
- `hsameCell` and `hside` are hypotheses because of ghw-charp2's (A) patch: same-cell unbound darts exist, so the
  module calls neither `alpha_faceOf_not_cell_of_unbound` nor `sum_card_unboundOffRegions_le`.
- `exists_class_of_relatorSide` is proved here from `sides_eq` and `kind_eq`, so the producer does not supply it.
- hull-count94 found that T is not independent of ε. Pendant same-cell trees at interior vertices of region sides
  are unbound, so T is about 24(ε+1)⌈(c+2)/λ⌉₊. They proposed respelling `OsinLemma94ClassCountInput` as `∃ K L`.
  The lemma takes any T, so it is unaffected.
- Consumer: hull-count94's producer of Q (Estimating/OsinLemma94ClassJoins, unlanded).

## Bad-junction exclusion (09-13): the planar half
The lead assigned the bad-junction exclusion. fff-periodic owns the Prop, and this lane writes it.
- Model test, sent to hull-count94: the "at least 2 non-joins" filter fails on a spur inside a bubble. The exclusion
  that holds is "at most one same-cell junction of a polygon is not a join", and it needs no DartMinimal.
- GGT/VanKampen/Estimating/OsinLemma94JunctionPocket (GREEN 0913-170620-78416; landed with this report; in the wire
  queue), at CombMap level. A junction is `hb : σ b = α a`, `hab : facePerm^(m+1) a = b` with `hleast` (m least),
  `hm : m ≠ 0`, and `hface : faceOf (α b) ≠ faceOf a`. The split map is `FoldMap.joined M (facePerm^m a) a`.
  - `reach_or_reach (hM : M.IsConnected) p e x`: after any join, every dart is reached from `facePerm p` or
    `facePerm e`.
  - `not_reach`, `junction_not_reach`: the face side (from b) and the gap side (from `facePerm a`) are apart. The
    proof goes through `PinchLemma.split_euler`.
  - `reach_gap`, `reach_face`: the gap is on the gap side, and the face across the corner is on the face side.
  - `gap_alpha_faceOf_ne`: (B) the reversed gap avoids the walk of the face.
  - `reach_face_or_reach_face`: (C1) of two junctions of one face with different b, every dart is on the face side of
    one of them. So a given dart, such as one on the outer face, is on the gap side of at most one junction.
- Open for the exclusion Prop:
  - the polygon-level spelling, which waits on hull-count94's `J k s` (Estimating/OsinLemma94ClassJoins, unlanded);
  - value one of the gap. `closedWalk_value_eq_one_of_gCells` (GGT/VanKampen/ClosedWalkValue) needs a
    `FaceAssembly`, and the general `RegionFaceAssemblyStatement` is an unproved binder.

## Next
The polygon-level exclusion over `J k s`, and a value-one route for the gap loop.
