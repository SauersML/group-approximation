# ghw-charp2 lane report

## Scope (roster, 09-13)

Closed GHWCharP, the positive-characteristic places of GHW Theorem 4, at the Prop the 857f7e44a
reduction consumes: `GroupApproximation.GHW.GHWFinitelyGeneratedCharP`
(`Kazhdan/GHWTheoremFour.lean`),
`∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
Printed sentence: tex 1146--1147, "Every countable subgroup of $\mathrm{GL}_2$ over a field has the Haagerup
property~\cite[Theorem~4]{GHW}".  `GHWTheoremFour` itself belongs to ghw-assembly.

## Status: CLOSED

- `theorem ghwFinitelyGeneratedCharP : GHWFinitelyGeneratedCharP` (`Kazhdan/GHWCharPClosed.lean`), with
  `#audit_closed_axioms`.  ghw-assembly reports the audit as `[propext, Classical.choice, Quot.sound]`.
- `theorem printedGHWTheoremFourCharP : PrintedGHWTheoremFourCharP` (`Kazhdan/GHWCharP.lean`): the printed clause over
  fields of prime characteristic, `∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (Γ : Subgroup (GL (Fin 2) F)), Countable Γ → HasHaagerupProperty.{0, 0} Γ`,
  with `#audit_closed_axioms`.
- Compiled evidence: probe 0913-013742-23843 (run by ghw-assembly; base 79102e615; mods `GHWTheoremFour`,
  `GHWCharPClosed`) is PROBE GREEN.  Its only overlay was `GHWFiniteReduction` (md5 8fc833fd), which is byte-equal to
  origin since ghw-assembly's c2a587f4f.  The import closure of `GHWCharPClosed` has 109 GroupApproximation modules.
  Of these, only `GHWFiniteReduction` changed between 79102e615 and origin b490bf08d, so the origin bytes are the
  green bytes.

## Files

- `GroupApproximation/Kazhdan/GHWCharP.lean`. This is the jacobson draft of 09-12 10:49, byte-identical to
  `attic/sweep-2026-09-12/GroupApproximation/Kazhdan/GHWCharP.lean.txt`; no lane file list claimed it.
  - `hasHaagerupProperty_closure_of_charP`: the finitely generated case.
  - `printedGHWTheoremFourCharP`: countable subgroups in prime characteristic.
- `GroupApproximation/Kazhdan/GHWCharPClosed.lean`, new: `ghwFinitelyGeneratedCharP`.  It is separate so that
  `GHWCharP` does not import `GHWTheoremFour`.
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

- 7155865b2: `Kazhdan/GHWCharP.lean`, `Kazhdan/GHWCharPClosed.lean`.  Landed unverified; they now compile green
  (above), with no Lean bytes changed since.
- 4626c73f2: this report (first version).

## History

- My own probe of `GHWCharP` and `GHWCharPClosed` failed only in `GHWFiniteReduction`.  Two lines were wrong:
  `Subgroup.map_closure` does not exist at the pin (it is `MonoidHom.map_closure`), and there was a
  `congrArg Subtype.val` type mismatch.  ghw-assembly fixed both at c2a587f4f.
- I also wrote a local rewrite of `GHWCharP`, which was not needed: the origin bytes compile.  I discarded it
  (lane backup only) and landed no Lean change.

## Census

- Row b6d1590be7ab (L1145, graded by ghw-assembly): a `partial` row citing `ghwFinitelyGeneratedCharP`,
  `printedGHWTheoremFourCharP` and `hasHaagerupProperty_closure_of_charP`
  (`metadata/nm-census-rows/ghw-charp2.tsv`).

## Wiring

- Queued `GroupApproximation.Kazhdan.GHWCharPClosed ghw-charp2 7155865b2`.  Its unwired chain is `GHWCharP`,
  `GHWTheoremFour`, `GHWFiniteReduction`, `BoundedIntegralFinite`, `GHWFrobeniusSeparable`, `TotalDegreeValuation`
  and `ValuationExtensionPlaces`.

## Residual (exact)

- None for this lane.
- The printed sentence over every field still needs `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
  This is dgo-geometric's GHWCharZeroFiniteness, assembled by ghw-assembly.

## Next

- Scope finished; waiting for the next item from the lead.
