# ghw-charp2 lane report

## Scope (roster, 09-13)

Closed GHWCharP, the positive-characteristic places of GHW Theorem 4, at the Prop the 857f7e44a
reduction consumes: `GroupApproximation.GHW.GHWFinitelyGeneratedCharP`
(`Kazhdan/GHWTheoremFour.lean`),
`∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
Printed sentence: tex 1146--1147, "Every countable subgroup of $\mathrm{GL}_2$ over a field has the Haagerup
property~\cite[Theorem~4]{GHW}".  `GHWTheoremFour` itself belongs to ghw-assembly.

## Files

- `GroupApproximation/Kazhdan/GHWCharP.lean`. This is the jacobson draft of 09-12 10:49, byte-identical to
  `attic/sweep-2026-09-12/GroupApproximation/Kazhdan/GHWCharP.lean.txt`; no lane file list claimed it.
  - `hasHaagerupProperty_closure_of_charP`: the finitely generated case.
  - `printedGHWTheoremFourCharP : PrintedGHWTheoremFourCharP`: countable subgroups in prime characteristic.
- `GroupApproximation/Kazhdan/GHWCharPClosed.lean`, new: `theorem ghwFinitelyGeneratedCharP : GHWFinitelyGeneratedCharP`
  with `#audit_closed_axioms`.  It is separate so that `GHWCharP` compiles even if `GHWTheoremFour` is red.
- `GroupApproximation/Kazhdan/GHWEntries.lean`: an older unowned draft in the shared tree and the attic.
  `GHWCharP` does not use it.

## Route (printed GHW route, no literature input)

1. The entries of `s` and of their inverses generate a finitely generated `𝔽_p`-algebra `A`, and every element
   of `⟨s⟩` has its entries in `A`.
2. Noether normalization (`exists_integral_inj_algHom_of_fg`, Mathlib) gives `B = 𝔽_p[t_1..t_d] ↪ A`, integral.
3. `K = L(entries)` with `L = Frac B` is finite over `L`.  An iterated Frobenius maps `K` into a separable
   intermediate field `K'` (`GHWFrobeniusSeparable`, on main, green).
4. The places of `K'` over the total-degree place of `L` leave only finitely many integral elements of bounded
   valuation.  This is `BoundedIntegralFinite.finite_bounded_integral` (on main, green, jacobson 19441736f); it
   uses `ValuationExtensionPlaces` and `TotalDegreeValuation` (green 22f1987d0).
5. `hasHaagerupProperty_of_places` (`GHWPlaces`, root-wired) with no archimedean places.

## Landed

- 7155865b2 (unverified, not wired): `Kazhdan/GHWCharP.lean`, `Kazhdan/GHWCharPClosed.lean`.

## Probe

- Probe of `GroupApproximation.Kazhdan.GHWCharP` and `GroupApproximation.Kazhdan.GHWCharPClosed` (clone lix-e) is
  running.  The closure also compiles `GHWFiniteReduction` (57023734b) and `GHWTheoremFour` (857f7e44a) for the
  first time; both were landed unverified.

## Residual (exact)

- None beyond compilation: the chain has no hypothesis binder.  `GHWFinitelyGeneratedCharP` closes once the probe is
  green and lands.

## Next

- Fix the probe errors, land green, and append census rows for LINE:1146 and LINE:1147 (the char-p half).
- Queue `GroupApproximation.Kazhdan.GHWCharPClosed` for wiring.
- Hand `ghwFinitelyGeneratedCharP` to ghw-assembly for `printedGHWTheoremFour`.
