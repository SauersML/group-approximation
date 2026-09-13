# fff-quotient (lane report, 2026-09-13)

Target (ROSTER): the remaining Hyde–Lodha Proposition 4.7 pieces, other than Lemma 4.6 (hl-lemma46) and
PiFinitePresentation (kh-ejz), closed.  Consumer: `hW : FinitelyPresentedInfiniteSimpleStatement`
(simple-group's `finitelyPresentedInfiniteSimpleStatement_of_stabK`, integration point
`FinitelyPresentedInfiniteSimpleLeaves`).

## Compiled and landed
- Green probe 0913-011512-60372 (bytes = origin/main, queued for wiring):
  - `HydeLodha/QTwoFinitePresentationRestrict` (7e652b78b): `perRestrictPerm`, `exists_upsilon_split`
    (an element of `Γ₂` supported in `(c, e) + ℤ` fixing `c, d` splits over `[c, d]` and `[d, e]`).
  - `HydeLodha/QTwoFinitePresentationStabKSplit` (87b137fd3): commuting pieces and casing bounds of
    `X_Γ(c, e, S) = Υ_Γ([c, e]) ∩ Γ_S`.
  - `HydeLodha/QTwoFinitePresentationStabK` (ec1a3f2ae): `UpsilonFinitelyPresented` (Lemma 4.6 as a
    named Prop), `isFinitelyPresented_upsilon_inf_stabK`, `isFinitelyPresented_stabK_of_upsilon`.
- Green probe 0913-011741-91887 (bytes = origin/main, queued for wiring): Lemma 4.5, `|I| = 1`, for `Γ₂`.
  - `HydeLodha/QTwoFinitePresentationGermGamma` (7c39b21cf): germs of `Γ₂` at fixed grid points.
  - `HydeLodha/QTwoFinitePresentationLong` (ddd327336): `isFinitelyPresented_upsilon_gammaTwo_long`
    (`Υ_{Γ₂}([a, a + 1])` finitely presented, ascending HNN extension over the short case).
- Green probe 0913-012814-68887 (bytes = origin/main, queued for wiring):
  `HydeLodha/QTwoPropositionFourSeven` (7494328a6): `stabK_eq_stabK_addIntSet`
  (`Γ_K = Γ_{K+ℤ}` for `Γ ≤ Γ₂`), `PrintedPropositionFourSeven`, `printedPropositionFourSeven_of_upsilon`.

## Residual
Lemma 4.6, `UpsilonFinitelyPresented`, is assembled on main by the lane owners, not by this lane:
`upsilonFinitelyPresented_of_dynamics` (QTwoLemmaFourSixAssembly 3e2e73c3d, simple-group; its `|I| = 1`
case generalizes `QTwoFinitePresentationLong` to `Q₂ ≤ Γ ≤ Γ₂`) and
`lemmaFourSixDynamics : LemmaFourSixDynamicsStatement` (QTwoLemmaFourSixDynamics de535e84c, landed
unverified, probe pending).  Once that probe is green, hW is
`finitelyPresentedInfiniteSimpleStatement_of_dynamics lemmaFourSixDynamics`
(FinitelyPresentedInfiniteSimpleClosed).

## Next
The `|I| = 1` item was already landed by simple-group; this lane wrote no draft for it.

W2 hbridge, the M2 certificate cut (lead, 2026-09-13): take one separable CutFaces piece that
hull-component has not started.  hull-component answered that none is left, and main confirms it:
- the side-designated cases are `CutMove.outcome_left` (CutOutcomeSides, 27f56e14b) and
  `CutMove.outcome_right` (CutOutcomeRight, 47b7225af), which also has `CutMove.outcome`
  (probe 0913-045018-55444 GREEN);
- the source of a cut face is debt-conditional's `letterStepBound_of_cutLiftOutcome`
  (LetterPullbackCut, 457c543a8), built on `exists_geodesicCut_of_leastAreaCertificates`;
- hull-bridge's LetterPullbackHolds and EmbeddedBridgeHolds are in flight.

This lane wrote no Lean for W2.

W1 (lead, ~08:30, the only open wall): help kh-ejz on `SectionPocketFaceSetInput`
(dgo-analytic's OsinPocketPieces, 9cb70824c), and ask kh-ejz for a sub-piece before writing anything.
Asked at ~08:40.  All three candidates would go in new fff-quotient modules:
1. target positions: the `t₂` arc of `outerDarts` between the ends of `a` and `b`, with `lo_le`/`le_hi`
   against `cuts.cut j.castSucc` and `cuts.cut j.succ`, from `TargetsSectionIndex`;
2. carrier bridge: a `PocketRegion` with FollowsBoundary, the `s₁ t₁ s₂ t₂` split, the kept and source
   cells and the ε bounds, giving `Nonempty (PocketFaceSet …)`;
3. side bounds on the two region sides of an `exteriorAt` candidate.
This lane also asked whether dgo-analytic's restatement after the pinch, region, collar reorder
keeps `PocketFaceSet`.  No Lean is written until kh-ejz answers.

## Census
No row: these modules prove the cited group consumed at tex 1679 and do not carry a sentence (same
grading as simple-group).
