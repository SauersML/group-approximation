# ghw-charp2 lane report

## Scope (lead, 09-12 ~10:30)

Assemble GHW Theorem 4, the first clause of tex 1146--1147 (remark after `prop:torsion-defect-ring`):
"Every countable subgroup of $\mathrm{GL}_2$ over a field has the Haagerup property~\cite[Theorem~4]{GHW}".
jacobson handed over `GroupApproximation/Kazhdan/GHWTheoremFour.lean` (the union and final assembly). Census
rows to close: `b6d1590be7ab` and jacobson LINE:1146 / LINE:1147.

## Landed

- 857f7e44a (unverified): `GroupApproximation/Kazhdan/GHWTheoremFour.lean`, namespace `GroupApproximation.GHW`
  - `def PrintedGHWTheoremFour : Prop := ∀ (K : Type) [Field K] (Γ : Subgroup (GL (Fin 2) K)), Countable Γ → HasHaagerupProperty.{0, 0} Γ`
  - `def GHWFinitelyGeneratedCharP : Prop := ∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`
  - `def GHWFinitelyGeneratedCharZero : Prop := ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`
  - `theorem hasHaagerupProperty_closure_of_charP_charZero (hp) (h0) (K : Type) [Field K] (s) (hs : s.Finite)`: split on `CharP.char_is_prime_or_zero K (ringChar K)`
  - `theorem printedGHWTheoremFour_of_charP_charZero (hp : GHWFinitelyGeneratedCharP) (h0 : GHWFinitelyGeneratedCharZero) : PrintedGHWTheoremFour`: via `hasHaagerupProperty_of_closure_finite` (jacobson, GHWFiniteReduction, 57023734b)
- bf941beaf (unverified): corrects the docstring tex line range from 1145 to 1146.
- Probe of `GroupApproximation.Kazhdan.GHWTheoremFour` running on ring-b-end.

## Residual (exact)

- `GroupApproximation.GHW.GHWFinitelyGeneratedCharP`: jacobson, `GHWCharP.hasHaagerupProperty_closure_of_charP`. Not on origin yet.
- `GroupApproximation.GHW.GHWFinitelyGeneratedCharZero`: dgo-geometric, `GHWCharZero.hasHaagerupProperty_closure_of_charZero`, on top of sec2's green `hasHaagerupProperty_of_countable_places`. Not on origin yet.

## Next

- Probe `GroupApproximation.Kazhdan.GHWTheoremFour` on ring-b-end, then land it green.
- When both inputs are on origin, write `GHWTheoremFourClosed.lean` with `theorem printedGHWTheoremFour : PrintedGHWTheoremFour` and `#audit_closed_axioms`.
- Add census rows, and tell census-merge about `b6d1590be7ab` and jacobson 1146/1147.
