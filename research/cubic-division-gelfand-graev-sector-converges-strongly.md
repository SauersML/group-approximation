---
rg: 2
id: cubic-division-gelfand-graev-sector-converges-strongly
kind: claim
title: For the cyclic cubic division algebra over Q(2cos 2pi/7), the Gelfand--Graev representations of SL_3(F_p), pulled back to SL_1(O_D), converge strongly to the regular representation
distinct_from:
  cubic-division-congruence-representations-converge-strongly: that is the whole of l^2_0(SL_3(F_p)) for some D; this is the generic sector only (the Gelfand--Graev representations), for one fixed D, and misses the permutation representation on nonzero vectors.
  cubic-division-vector-sector-converges-strongly: that is the complementary vector sector, a permutation representation with Chebotarev statistics at fixed length; this sector is monomial, and its fixed-length traces vanish at large p.
---

OPEN.  Let `D_7`, `O_D`, `Gamma_D` and `P_D` be as in `cubic-division-vector-sector-converges-strongly`.
For primes `p` not in `P_D`, let `GG_p` be the sum over `a in F_p^x / F_p^x3` of `Ind_U^(SL_3(F_p)) psi_a`, as in
`cubic-division-congruence-norm-splits-into-two-sectors`, pulled back to `Gamma_D`.

Claim: `||GG_p(z)|| -> ||lambda_(Gamma_D)(z)||` for every `z in C[Gamma_D]`, as `p -> infinity` over primes.

- The lower bound holds (part 2 of the splitting node), so only outliers are at stake.
- `GG_p` contains every generic irreducible representation of `SL_3(F_p)`, among them the cuspidal ones,
  the constituents of the Steinberg representation and the irreducible principal series.  It contains no
  other irreducible.
- Together with `cubic-division-vector-sector-converges-strongly`, this claim is equivalent to the target
  for `D_7` (`cubic-division-congruence-sc-from-two-sectors`).

## Attempts

* **Trace reformulation.**  Not a proof.  For a free pair, no outlier for the generator sum is equivalent
  to square-root cancellation at lengths `n >> log p` in
  `(p^2-1)(p^3-1) I_p(n) - (p^2-1) Tr_p(n) + R_p(n)`.  This counts cyclically reduced words that are the
  identity, a transvection or regular unipotent mod `p` (splitting node, part 4).
  - Under equidistribution the three terms are each of size `3^n / p^2` and cancel exactly.
  - At fixed `n` the traces vanish for large `p`, so no averaging over primes, and no Chebotarev
    statistics, can say anything.
* **Multiplicity and girth.**  Dies at a constant factor, as in the vector sector.  Generic constituents
  have dimension at least `(p-1)^2 (p+1) / 3`, but the girth is only `c log p`.  This gives
  `mu <= 2 sqrt 3 exp(O(1/c))`.
* **Uniform gap.**  Property (T) of `Gamma_D` gives `||GG_p(Z)|| <= 4 - eps_0`, uniformly.  In the traces
  that is an exponential saving, not the square-root one.
* **Numerics.**  Evidence only.  This is the first test of any cuspidal sector for this algebra, on an
  explicit model of `SL_3(F_p)/U`: pairs `(v, w)` with a unitriangular cocycle.
  - The character formula was checked exactly at `p = 5, 7, 11, 13`.
  - At `p = 13`, dimension 368928 per sector, the certified pair `a^19, b^19` gives an extreme Ritz value
    of 3.4772 (excess +0.013 over `2 sqrt 3`) in all three sectors.  Random controls give +0.006 to +0.015.
  - `p = 13` is tiny, and `A mod 13` has order dividing 12.  The next split prime, `p = 29`, has dimension
    about `2e7` and did not fit the computation cap
    (`research/artifacts/cubic-division-congruence-norm-splits-2026-09-16.md`, Section 6).
