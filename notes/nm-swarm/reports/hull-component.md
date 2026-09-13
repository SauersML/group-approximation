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

## Next
hull-unbound closes `QuasiGeodesicRespellInput` with this theorem. Asking the lead for the next item.
