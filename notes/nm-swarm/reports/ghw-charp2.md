# ghw-charp2 lane report

## Item 4 (09-13): Jacobson probe record and the GHW char-0 archimedean split

Lead order:
1. `JacobsonComplementarySentence` has no probe record or queue line, and jacobson is silent.  Probe it at the
   current base without editing it, queue it under ghw-charp2, and send the tag to root-wire.
2. Split the char-0 archimedean half directly with ghw-assembly.  `Kazhdan/GHWCharZero.lean` is ghw-assembly's
   unlanded work in progress: no edits and no parallel copy.  Take only a piece ghw-assembly names, in my own module.

### Jacobson record: DONE

- Probe 0913-040230-50292 at base 42d443298 named
  `GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonComplementarySentence`.  Result: PROBE GREEN, EXIT=0.
- The probe rebuilt 0 modules; lake found the trace up to date and used the cached olean.  The clone's source md5
  (89f64931) equals origin and the base.  Origin has not changed the module, `FullDefectRingEJZUnconditional` or
  `JacobsonFiniteMatrices` since the base.
- The module is on origin, not in the ghw-charp2 overlay, so the green record lists only ghw-charp2 files.
- Queued `GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonComplementarySentence ghw-charp2 42d443298`, with a
  comment line above it giving the tag.  root-wire has the tag and the caveat.

### Archimedean split: bridge landed; ghw-assembly's call site needs no change

- Background: ghw-assembly's on-disk `Kazhdan/GHWCharZero.lean` (saved 03:52) expected the old shape at lines
  368--372.  I proposed the bridge below to fix that with a one-line call.  The lead then ordered: land the bridge
  now in my own module without waiting for ghw-assembly, land exactly the probed bytes, and send ghw-assembly the
  name.
- Landed 86635025c: `GHW.exists_intPoly_eq_pow_mul_minpoly_coeff d M N hM hn a h i`, appended to
  `Kazhdan/GHWCharZeroPlaces.lean`, which has been root-wired since ce699b9b8.  The change is additive: no existing
  statement changed, and the name is new on origin and on disk.
  - Setup: `B = ℤ[t_1..t_d]`, `L = Frac B`, `K/L` finite with `finrank L K = n`, and `M > 0`.
  - Claim: suppose every coefficient of `minpoly L (M^N a)` is `algebraMap G` for some `G ∈ ℤ[t]` of total degree at
    most `N·n`.  Then so is `M^(N·n)` times every coefficient of `minpoly L a`.
  - Proof:
    - `c_i(M^N a) = M^(N(deg − i)) c_i(a)`, by `IsIntegrallyClosed.minpoly_smul` and `coeff_scaleRoots`;
    - `deg − i ≤ n`;
    - the witness is `M^(N(n − (deg − i))) · G`;
    - the degree bound is `totalDegree_mul` with `totalDegree_C`.
- Compiled evidence: probe 0913-044256-36897 (base 27f56e14b) is PROBE GREEN.
  - `GHWCharZeroPlaces` and `IntegerPlacesMinpoly` are BUILT, with 0 warnings.
  - The bridge depends on `[propext, Classical.choice, Quot.sound]`.
  - The landed bytes are the green bytes (md5 cd60c1fc).
- Premise change: ghw-assembly landed `Kazhdan/GHWCharZero.lean` at add35a53a (04:20; unverified, unwired).
  - Its call site (lines 371--378) now passes the scaled elements `M^N x` to `finite_of_minpoly_coeff` through
    `Set.Finite.of_finite_image`.
  - `finite_of_minpoly_coeff` no longer carries the `M^(N n)` factor.
  - So the line-372 break is gone and the one-line replacement is obsolete.  I sent ghw-assembly the name, the SHA
    and the signature, and said that no change is needed.

## Item 3 (09-13): the additive non-archimedean places for GHWFinitelyGeneratedCharZero

Lead order: take the unstarted piece of the residual `GHWFinitelyGeneratedCharZero`, after settling the file name and
the interface lemma with ghw-assembly.  ghw-assembly had already landed the grid finiteness (`Algebra/IntegerGridFinite`,
3108f1cc7) and started the archimedean places.  It proposed the non-archimedean statement below for ghw-charp2, and I
accepted it verbatim.

### Status: CLOSED (interface lemma; this item has no endpoint Prop)

- Compiled evidence: probe 0913-033545-85262 (base a4c5b47db) is PROBE GREEN, with `GHWCharZeroPlaces` and
  `IntegerPlacesMinpoly` BUILT.  All four declarations depend on `[propext, Classical.choice, Quot.sound]`.  The
  landed bytes are the probed bytes.

- `GroupApproximation/Algebra/IntegerPlacesMinpoly.lean` (new): `IntegerPlacesMinpoly.exists_places_minpoly_coeff d K hM`.
  - Setup: `B = ℤ[t_1..t_d]`, `L = Frac B`, `K/L` finite (`K : Type`, `[CharZero K]`), and `M > 0`.
  - Claim: there are additive valuations `v : Fin r → AddValuation K (WithTop ℤ)` and uniformizers `π` with
    `v j (π j) = 1` with this property.  Suppose `M^k b` is integral over `B` for some `k` and `-N ≤ v j b` for every
    `j`.  Then every coefficient of `minpoly L (M^N b)` is `algebraMap G` for some `G ∈ ℤ[t]` of total degree at
    most `N·[K:L]`.
- `Kazhdan/GHWCharZeroPlaces.lean`, restated.  By rule 22, no declaration outside the file uses the old statements.
  - The place bound is sharpened to `w c_i ≤ exp (N·(deg − i))`, in `_le` and in `_le_family`.
  - `GHW.exists_places_minpoly_coeff` now says that the coefficients of `minpoly L (M^N a)` are integer polynomials of
    total degree at most `N·[K:L]`.  The old statement was about `M^(N·[K:L]) c_i(a)`.

### Route

- Scaling: `c_i(M^N a) = M^(N(deg−i)) c_i(a)` (`IsIntegrallyClosed.minpoly_smul`, `coeff_scaleRoots`).
- Valuation bounds:
  - at `p | M`, the sharp bound gives `v_p(c_i(M^N a)) ≤ exp(−N(deg−i))·exp(N(deg−i)) = 1`;
  - at the degree place, `c_i(M^N a) ≤ exp(N(deg−i)) ≤ exp(N·[K:L])`.
- Integrality: `M^k·M^N a` is integral, so the coefficients of `minpoly B` of it lie in `B` and equal
  `M^(k(deg'−i)) c_i(M^N a)`.  `exists_algebraMap_eq` then clears the `p | M` denominators.
- Additive form: `ValuationWithTopInt.addVal`, `addVal_eq_one` and `neg_le_addVal_iff`.  The case `b = 0` is trivial.

### Landed

- 0379bac08: `Algebra/IntegerPlacesMinpoly.lean` (new) and the restated `Kazhdan/GHWCharZeroPlaces.lean`.  This was a
  normal landing on the green record 0913-033545-85262.  ghw-assembly has the SHA and the signature.

### Census and wiring

- Row b6d1590be7ab now also cites `IntegerPlacesMinpoly.exists_places_minpoly_coeff`.  It stays `partial`, because the
  char-0 Prop is open.
- Queued `GroupApproximation.Algebra.IntegerPlacesMinpoly ghw-charp2 0379bac08`.  It imports `GHWCharZeroPlaces`,
  which imports `IntegerGaussValuations`.

### Residual (exact)

- None for this item.
- Still open, owned by ghw-assembly (the archimedean places over grid points, Noether normalization over ℚ, and the
  assembly through `hasHaagerupProperty_of_countable_places`; the grid finiteness `IntegerGridFinite` has landed):
  `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.

## Item 2 (09-13): places over ℚ(t_1..t_d) for GHW characteristic 0

Lead order: characteristic 0 belongs to ghw-assembly, which owns the grid/Nullstellensatz finiteness, the archimedean
places and the assembly.  ghw-charp2 builds the non-archimedean places over ℚ (the degree place, the places over
p | M, `exists_places_over`) on the char-p template.  Printed sentence: tex 1146--1147, the GHW Theorem 4 clause.

### Status: CLOSED (lemmas; this item has no endpoint Prop)

- Superseded statements: Item 3 (0379bac08) restated the three lemmas below.  The bound is now `exp (N·(deg − i))`, and
  `exists_places_minpoly_coeff` is about the coefficients of `minpoly L (M^N a)`.  The descriptions below are the
  d2cf04137 versions.

- `GroupApproximation/Kazhdan/GHWCharZeroPlaces.lean` (new):
  - `GHW.exists_places_minpoly_coeff_le`.  Setup: a place `w` of `L` with uniformizer `π`, and `K/L` finite
    separable.  Claim: there are finitely many places `u j` of `K`, each with a uniformizer.  If `u j a ≤ exp N` for
    every `j`, then `w` of every coefficient of `minpoly L a` is at most `exp (N · [K:L])`.
  - `GHW.exists_places_minpoly_coeff_le_family`: the same claim for a finite family of places of `L` at once.
  - `GHW.exists_places_minpoly_coeff d M hM K`.  Setup: `B = ℤ[t_1..t_d]`, `L = Frac B`, `K/L` finite, `M > 0`.
    Claim: there are finitely many places `u j` of `K`, each with a uniformizer.  Suppose `M^e a` is integral over
    `B` and `u j a ≤ exp N` for every `j`.  Then each coefficient `c_i` of `minpoly L a` satisfies
    `M^(N·[K:L]) c_i = G` for some `G ∈ ℤ[t]` of total degree at most `N·[K:L]`.  The places lie over the degree
    place (when `d > 0`) and the `p`-adic places for `p | M`.  Separability is automatic in characteristic 0.
- `GroupApproximation/Algebra/IntegerGaussValuations.lean` (claimed; an orphan from de485d673, in no lane's file
  list): the `p`-adic and total-degree valuations on `ℚ(t_1..t_d)` and clearing denominators
  (`exists_algebraMap_eq`).
  - It had never compiled: `FiniteMultiplicity.of_prime_left` needs `WfDvdMonoid (MvPolynomial (Fin d) ℤ)`.
  - Fixed by importing `Mathlib.Algebra.EuclideanDomain.Int` and `Mathlib.RingTheory.PrincipalIdealDomain`.
- Compiled evidence: probe 0913-024239-39237 (base 3e34da4ea) is PROBE GREEN, with both modules BUILT.
  `exists_places_minpoly_coeff` depends on `[propext, Classical.choice, Quot.sound]`.  The earlier probe
  0913-022359-56894 failed only in IntegerGaussValuations, on the missing instance.

### Route

1. Single place.  `ValuationExtension.exists_places_over` gives the places `u j` over `w`: `u j π < 1`, and an
   element integral at every `u j` has `w`-integral minpoly coefficients.  `π^N a` has `u j ≤ 1`, and
   `IsIntegrallyClosed.minpoly_smul` with `coeff_scaleRoots` gives `w(c_i)·exp(−N(deg−i)) ≤ 1`.
2. Family: `choose`, then `Fintype.equivFin (Σ t, Fin (r t))`.
3. Over ℚ(t):
   - The base places are indexed by `{p // p ∈ M.primeFactors} ⊕ Fin (min d 1)`.
   - `minpoly B (M^e a)` has coefficients in `B` (`minpoly.isIntegrallyClosed_eq_field_fractions'`), equal to
     `M^(e(deg−i)) c_i`.
   - Clearing the `p | M` denominators (`exists_algebraMap_eq`) gives `G`.
   - The degree bound is `degValuation_algebraMap_le_iff`; when `d = 0`, `G` is constant.

### Consumer interface (ghw-assembly)

- `GHWCountablePlaces` takes `AddValuation K (WithTop ℤ)`.  Use:
  - `ValuationWithTopInt.addVal (u j)`;
  - `addVal_eq_one` for the uniformizers;
  - `neg_le_addVal_iff` for the bounds, as in `GHWCharP.hasHaagerupProperty_of_isIntegral`.
- ghw-assembly owns the finiteness of the grid of `G` (Combinatorial Nullstellensatz) and the archimedean places.

### Landed

- d2cf04137: `Kazhdan/GHWCharZeroPlaces.lean`.  Landed unverified; it is green now with the same bytes.
- 321615044: the `Algebra/IntegerGaussValuations.lean` import fix.

### Census and wiring

- Row b6d1590be7ab now also cites the three places lemmas.  It stays `partial`: the char-0 half is open.
- Queued `GroupApproximation.Kazhdan.GHWCharZeroPlaces ghw-charp2 321615044`.  `IntegerGaussValuations` is unwired;
  `BoundedIntegralFinite` and `ValuationExtensionPlaces` are in the `GHWCharPClosed` chain.

### Residual (exact)

- None for this item.
- Still open, owned by ghw-assembly (grid finiteness, archimedean places, assembly):
  `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.

## Item 1 (closed): GHWFinitelyGeneratedCharP

### Scope (roster, 09-13)

Closed GHWCharP, the positive-characteristic places of GHW Theorem 4, at the Prop the 857f7e44a
reduction consumes: `GroupApproximation.GHW.GHWFinitelyGeneratedCharP`
(`Kazhdan/GHWTheoremFour.lean`),
`∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
Printed sentence: tex 1146--1147, "Every countable subgroup of $\mathrm{GL}_2$ over a field has the Haagerup
property~\cite[Theorem~4]{GHW}".  `GHWTheoremFour` itself belongs to ghw-assembly.

### Status: CLOSED

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

### Files

- `GroupApproximation/Kazhdan/GHWCharP.lean`. This is the jacobson draft of 09-12 10:49, byte-identical to
  `attic/sweep-2026-09-12/GroupApproximation/Kazhdan/GHWCharP.lean.txt`; no lane file list claimed it.
  - `hasHaagerupProperty_closure_of_charP`: the finitely generated case.
  - `printedGHWTheoremFourCharP`: countable subgroups in prime characteristic.
- `GroupApproximation/Kazhdan/GHWCharPClosed.lean`, new: `ghwFinitelyGeneratedCharP`.  It is separate so that
  `GHWCharP` does not import `GHWTheoremFour`.
- `GroupApproximation/Kazhdan/GHWEntries.lean`: an older unowned draft in the shared tree and the attic.
  `GHWCharP` does not use it; the lead landed it as an orphan and ghw-assembly owns its dedupe.

### Route (printed GHW route, no literature input)

1. The entries of `s` and of their inverses generate a finitely generated `𝔽_p`-algebra `A`, and every element
   of `⟨s⟩` has its entries in `A`.
2. Noether normalization (`exists_integral_inj_algHom_of_fg`, Mathlib) gives `B = 𝔽_p[t_1..t_d] ↪ A`, integral.
3. `K = L(entries)` with `L = Frac B` is finite over `L`.  An iterated Frobenius maps `K` into a separable
   intermediate field `K'` (`GHWFrobeniusSeparable`, on main, green).
4. The places of `K'` over the total-degree place of `L` leave only finitely many integral elements of bounded
   valuation.  This is `BoundedIntegralFinite.finite_bounded_integral` (on main, green, jacobson 19441736f); it
   uses `ValuationExtensionPlaces` and `TotalDegreeValuation` (green 22f1987d0).
5. `hasHaagerupProperty_of_places` (`GHWPlaces`, root-wired) with no archimedean places.

### Landed

- 7155865b2: `Kazhdan/GHWCharP.lean`, `Kazhdan/GHWCharPClosed.lean`.  Landed unverified; they now compile green
  (above), with no Lean bytes changed since.
- 4626c73f2: this report (first version).

### History

- My own probe of `GHWCharP` and `GHWCharPClosed` failed only in `GHWFiniteReduction`.  Two lines were wrong:
  `Subgroup.map_closure` does not exist at the pin (it is `MonoidHom.map_closure`), and there was a
  `congrArg Subtype.val` type mismatch.  ghw-assembly fixed both at c2a587f4f.
- I also wrote a local rewrite of `GHWCharP`, which was not needed: the origin bytes compile.  I discarded it
  (lane backup only) and landed no Lean change.

### Census

- Row b6d1590be7ab (L1145, graded by ghw-assembly): a `partial` row citing `ghwFinitelyGeneratedCharP`,
  `printedGHWTheoremFourCharP` and `hasHaagerupProperty_closure_of_charP`
  (`metadata/nm-census-rows/ghw-charp2.tsv`).

### Wiring

- Queued `GroupApproximation.Kazhdan.GHWCharPClosed ghw-charp2 7155865b2`.  Its unwired chain is `GHWCharP`,
  `GHWTheoremFour`, `GHWFiniteReduction`, `BoundedIntegralFinite`, `GHWFrobeniusSeparable`, `TotalDegreeValuation`
  and `ValuationExtensionPlaces`.

### Residual (exact)

- None for this item.

## Next

- Item 3 is closed and landed (0379bac08).
- Item 4, Jacobson record: done.  Probe 0913-040230-50292 is queued, and root-wire has the tag.
- Item 4, archimedean split: the bridge `GHW.exists_intPoly_eq_pow_mul_minpoly_coeff` is landed (86635025c) and
  green.  ghw-assembly has the name and needs no piece from me; `Kazhdan/GHWCharZero.lean` stays untouched.
- Residual, owned by ghw-assembly: `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
  Its producer `ghwFinitelyGeneratedCharZero` is on main at add35a53a but has no probe record yet.
- Waiting for the lead's next item.
