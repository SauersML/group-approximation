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
hull-component, the owner, has not started.  On main: CutFaces (d62ea043a, 74c6b03ff) and CutSides
(74c6b03ff: `CutFace.left_val_mem`, `right_val_mem`, `arc_val_mem`; `left_designated` and
`right_designated` are marked in flight).  Proposed to hull-component, each in a new module of this lane:
- (a) `CutFace.right_designated`, a letter of `R` sharing its coset with an arc letter `b` has inverse
  value `X · b.val · Y` over bounded products (via `exists_designated_of_face`, `false_of_crossCoset`);
- (b) a `CutFace` with the arc rotated first, from `exists_geodesicCut_of_leastAreaCertificates`
  (LetterMoves), `IsSmallCancellation.admissible` and `List.rotate_append_length_eq`.

No Lean is written until hull-component names the piece.  Then the statement lands first, the proof
second, and only the new module is probed.

## Census
No row: these modules prove the cited group consumed at tex 1679 and do not carry a sentence (same
grading as simple-group).
