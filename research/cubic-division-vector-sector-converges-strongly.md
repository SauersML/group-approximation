---
rg: 2
id: cubic-division-vector-sector-converges-strongly
kind: claim
title: For the cyclic cubic division algebra over Q(2cos 2pi/7), the representations of SL_1(O_D) on mean-zero functions on nonzero vectors mod p converge strongly to the regular representation
distinct_from:
  cubic-division-free-pair-p2-schreier-asymptotically-ramanujan: that is one element (a free-pair generator sum) in one sub-sector (P^2); this is every group-ring element on all of l^2_0(F_p^3 minus 0), which contains P^2 and every other degenerate principal series.
  cubic-division-congruence-representations-converge-strongly: that is the whole of l^2_0(SL_3(F_p)) for some D; this is the vector sector only, for one fixed D, and misses every generic representation.
---

OPEN.  Let `D_7 = (K/Q, sigma, 2)` with `K = Q(2 cos 2pi/7)`, the division algebra of
`experiments/cubic-division-sc/sc_p2.c`.  Let `O_D` be a maximal order, `Gamma_D = SL_1(O_D)`, and `P_D` as in
`cubic-division-congruence-representations-converge-strongly`.  For primes `p` not in `P_D`, let
`sigma_p^0 = l^2_0(F_p^3 minus 0)`, pulled back along `Gamma_D -> SL_3(F_p)`.

Claim: `||sigma_p^0(z)|| -> ||lambda_(Gamma_D)(z)||` for every `z in C[Gamma_D]`, as `p -> infinity` over primes.

The lower bound holds (`cubic-division-congruence-norm-splits-into-two-sectors`, part 2), so only outliers
are at stake.  `sigma_p^0` is the sum of `l^2_0(P^2(F_p))` and the `p - 2` irreducible degenerate principal
series `Ind_P(chi o alpha)`, `chi != 1`.  Together with
`cubic-division-gelfand-graev-sector-converges-strongly`, this claim is equivalent to the target for `D_7`
(`cubic-division-congruence-sc-from-two-sectors`).

## Attempts

* **Trace reformulation.**  Not a proof.  For a free pair and its generator sum, no outlier is
  equivalent to square-root cancellation at lengths `n >> log p` in
  `(p-1) N_p(n) + (p^2-p) U_p(n) + (p^3-p^2) I_p(n) - |CR_n|`, where `N_p(n)` counts words with
  `p | Trd(w^-1) - Trd(w)` (`cubic-division-ihara-traces-count-roots-mod-p`, part 4(b)).  Effective
  Chebotarev reaches only `n = O(log p)`, and only on average over primes (see the `P^2` claim).
* **Multiplicity and girth.**  Dies at a constant factor.
  - The constituents have dimension at least `p^2 + p`.
  - The Cayley graph of `SL_3(F_p)` on a free pair has girth `c log p`, so closed-walk counts are free
    up to length `c log p`.
  - An eigenvalue `mu` in a constituent of dimension `m` gives `m mu^(2n) <= |G| (2 sqrt 3)^(2n) poly(n)`
    for `2n < c log p`.  So `mu <= 2 sqrt 3 exp(O(1/c))`, a constant factor above the regular norm.
    Beating it needs lengths `n >> log p`, where the identity count `I_p(n)` is itself the open problem.
* **Localised outliers.**  Excluded on `P^2` at logarithmic scale
  (`cubic-division-congruence-outliers-delocalise-at-log-scale`); the random half, high-trace
  cancellation, is missing.
* **Numerics.**  Evidence only.
  - For the certified pair `a^19, b^19 <= SL_1(Lambda)`, over 13 split primes up to 211, with 3 elements and
    random controls, the excess stays within the controls
    (`research/artifacts/cubic-ihara-bass-numerics-2026-09-13.md`, Job 2).
  - At `p = 13` the extreme Ritz value is 3.5416 against controls 3.4425--3.5562
    (`research/artifacts/cubic-division-congruence-norm-splits-2026-09-16.md`, Section 6).
