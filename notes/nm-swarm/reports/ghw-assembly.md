# ghw-assembly lane report

Target (census2 U4, tex L1145/1146): `PrintedGHWTheoremFour` (the roster spelling
`PrintedGHWTheorem4`), `∀ (K : Type) [Field K] (Γ : Subgroup (GL (Fin 2) K)), Countable Γ →
HasHaagerupProperty.{0,0} Γ`, closed.

## State (2026-09-13)

- `GroupApproximation/Kazhdan/GHWFiniteReduction.lean` (claimed by this lane): two red lines fixed
  (`Subgroup.map_closure` → `MonoidHom.map_closure`; the injectivity step now peels both subtype
  coercions). Probe 0913-013742-23843 GREEN: BUILT `GHWTheoremFour`, BUILT `GHWCharPClosed`;
  `ghwFinitelyGeneratedCharP` audits `[propext, Classical.choice, Quot.sound]`.
- `GHWTheoremFour` (on origin, no bytes changed) builds green:
  `printedGHWTheoremFour_of_charP_charZero (hp : GHWFinitelyGeneratedCharP)
  (h0 : GHWFinitelyGeneratedCharZero) : PrintedGHWTheoremFour`.
- `GHWCharPClosed` (ghw-charp2) builds green: `theorem ghwFinitelyGeneratedCharP :
  GHWFinitelyGeneratedCharP`, closed.

## Residual Prop

- `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)),
  s.Finite → HasHaagerupProperty.{0,0} (Subgroup.closure s)`. No producer on origin. Once it
  closes, `GHWTheoremFourClosed` is one line:
  `printedGHWTheoremFour_of_charP_charZero ghwFinitelyGeneratedCharP <char0>`.

## Char-0 route (design)

Template: `GHWCharP.hasHaagerupProperty_closure_of_charP`, with `ℚ` in place of `ZMod p`.

1. Entries of `s` generate a finitely generated `ℚ`-algebra `A`. Noether normalization gives an
   integral injection `MvPolynomial (Fin d) ℚ → A`; `K = L(entries)` is finite over
   `L = FractionRing (MvPolynomial (Fin d) ℤ)`.
2. Clear denominators: some integer `M > 0` makes every entry `M`-integral over
   `B = MvPolynomial (Fin d) ℤ`. `S = {a | ∃ j, IsIntegral B ((M : K) ^ j * a)}` is a subring
   containing the entries, the inverse determinants, and so `ρ(Γ)`.
3. Non-archimedean places: `IntegerGaussValuations.degValuation d` (d > 0) and
   `padicValuation d hp` for the primes `p ∣ M`, each extended to `K` by
   `ValuationExtension.exists_places_over`.
4. Archimedean places: `y : Fin d → ℂ`, algebraically independent over `ℚ`; the countable family
   `τ : K →+* ℂ` lying over the evaluations at the grid points `y + k`, `k : Fin d → ℤ`. There
   are finitely many over each point (`minpoly.AlgHom.fintype`).
5. Finiteness: minimal polynomial coefficients have bounded degree (degree place), bounded
   `p`-adic denominators (clear with `exists_algebraMap_eq`), and bounded values on the grid
   (`Polynomial.coeff_le_of_roots_le` plus `IntermediateField.exists_algHom_of_splits_of_aeval`).
   Integer polynomials of bounded degree with bounded values on a finite grid form a finite set
   (Combinatorial Nullstellensatz `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`).
6. Conclude with `GHW.hasHaagerupProperty_of_countable_places`.

Roster: dgo-geometric holds "closed GHWCharZeroFiniteness". This lane asked the lead whether to
build the char-0 producer.

## Landed

- GHWFiniteReduction fix + this report: see git log for `notes/nm-swarm/reports/ghw-assembly.md`.
