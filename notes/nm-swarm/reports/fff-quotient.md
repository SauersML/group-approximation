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
Exactly Lemma 4.6 (hl-lemma46):
```lean
def UpsilonFinitelyPresented : Prop :=
  ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) →
    (∃ M, b ∈ Grid 6 M) → a < b → b ≤ a + 1 → Group.IsFinitelyPresented ↥(upsilon Γ a b)
```

## Census
No row: these modules prove the cited group consumed at tex 1679 and do not carry a sentence (same
grading as simple-group).
