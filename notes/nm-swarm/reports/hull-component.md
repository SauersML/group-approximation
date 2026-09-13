# hull-component lane report

## Scope
Wall hbridge: `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}` from
`QuotientPeripheralLetterPullbackStatement` (GGT/HullSCLemma51EmbeddedProducer). hull-bridge integrates.
This lane owns (D), the letter pullback induction of Osin's Lemma 5.1, and its producer.

## Compiled on main (no hypotheses beyond the stated binders; `#audit_axioms` in each file)
- GGT/HullSCLemma51LetterPullbackAtoms: atoms, lifts of quotient relative balls, bounded products of images.
- GGT/HullSCLemma51LetterPullbackClose: `PullbackOutcome`, `mem_image_of_pullbackOutcome`.
- GGT/HullSCLemma51LetterPullbackRotate: `RotatedLift`, `exists_rotatedLift`. The predecessor's red fix
  d80e0d009 compiled green.
- GGT/HullSCLemma51LetterPullbackInduction: `LetterStepBound`, `.or`,
  `quotientPeripheralLetterPullbackAt_of_letterStepBound`.
- GGT/HullSCLemma51LetterPullbackShortcutArcs, GGT/HullSCLemma51LetterPullbackShortcut: the M1 move
  `letterStepBound_of_not_isRelGeodesic : LetterStepBound D W q hq (fun w => ¬ ∀ r, IsRelGeodesic D (w.rotate r))`.
  The predecessor left it untracked; it landed unverified at 0ad5acab1 and a fix landed at 22b893181.
- Probes: 0913-010957-99348 (Atoms, Close, Rotate, Induction, RelativeCosetPieces),
  0913-012328-36694 (ShortcutArcs, Shortcut, plus all of the above). All GREEN.
- Wire candidates queued.

## Residual Props
1. M2, the certificate cut: `LetterStepBound D W q hq (fun w => ∀ r, IsRelGeodesic D (w.rotate r))`, under
   hsc (`IsBoundedLemma44Input`), hmu, hrho, hker, hcert.
2. The producer `quotientPeripheralLetterPullbackStatement_holds : QuotientPeripheralLetterPullbackStatement`,
   from `(M1).or (M2)` and `quotientPeripheralLetterPullbackAt_of_letterStepBound`.

## Route for M2
Rotate the cut so that the arc comes first: `w.rotate r₀ = arc ++ tail`, with a face `ext = L · arc · R`,
`ext ++ rem ∈ W`, geodesic L, R, arc, and `|L| + |rem| + |R| < |arc|`. Rotated lift: `arc ++ tail = x ++ comp λ h⁻¹ :: y`.
The new quotient-null word is `respellInv L ++ respellInv rem ++ respellInv R ++ tail`.
- Letters of `respellInv rem` and `respellInv ext` are atoms.
- A side letter at the base coset: its face `L · arc · R · ext⁻¹` holds no other non-atom letter at its source
  coset. L and R are geodesic, and `false_of_crossCoset` separates L from R. Arc letters over the base coset
  are the designated letter or nothing.
- Case A (designated letter outside the arc): it stays designated.
- Case B (designated letter inside the arc):
  - no side letter shares its source coset: its face bounds `h`;
  - otherwise the unique side letter there becomes designated, with value `P₁ h⁻¹ P₂` over bounded `P₁`, `P₂`.

## Next
Modules GGT/HullSCLemma51LetterPullbackCutFaces (source faces),
GGT/HullSCLemma51LetterPullbackCutOutcome (quotient outcomes), GGT/HullSCLemma51LetterPullbackCut (M2),
GGT/HullSCLemma51LetterPullbackHolds (producer).
