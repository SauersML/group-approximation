---
rg: 2
id: sl2z-prime-congruence-quotients-converge-strongly
kind: claim
title: The mean-zero regular representations of SL_2(F_p), pulled back to SL_2(Z), converge strongly to the regular representation as p runs over primes
artifacts:
  - research/artifacts/sanov-congruence-spectra-2026-09-13.md
distinct_from:
  cubic-division-congruence-representations-converge-strongly: that is the canonical congruence sequence of a cocompact Kazhdan lattice in SL_3(R); this is the congruence sequence of the virtually free lattice SL_2(Z), which prime-level strong convergence for SL_3(Z) would force.
---

OPEN.  For every `z in C[SL_2(Z)]`,
`||l^2_0(SL_2(F_p))(z)|| -> ||lambda_(SL_2(Z))(z)||` as `p -> infinity` over
primes.  By induction and restriction this is equivalent to the same statement
for the Sanov free subgroup `F = <[[1,2],[0,1]], [[1,0],[2,1]]>`.  It includes
that the Cayley graphs of `SL_2(F_p)` for these generators have largest
nontrivial absolute eigenvalue tending to `2 sqrt 3`.

Why it matters.  `sl3z-prime-level-sc-forces-congruence-sc-for-sl2z`: if some
sequence of irreducible representations of `SL_3(F_(p_i))` converges strongly to
`lambda_(SL_3(Z))`, this claim holds along `p_i`.  So a refutation, i.e. one
`z` with a persistent outlier along all large primes, refutes prime-level strong
convergence for `SL_3(Z)`.  A proof would be explicit deterministic strong
convergence for a free group, which van Handel (arXiv:2510.12520, Section 2.2)
records as open.

## Attempts

* **Weak convergence (lower bound).**  Holds: normalized traces of
  `l^2_0(SL_2(F_p))` tend to the regular trace, so `liminf >= ||lambda(z)||`.  Only
  outliers are at stake.
* **Uniform gap.**  Known but not sharp: the Sanov subgroup has finite index in
  `SL_2(Z)`, so Selberg's `3/16` theorem (import) gives expansion.  It says
  nothing about the constant `2 sqrt 3`.
* **Numerics (2026-09-13).**  Artifact above; lower bounds from Lanczos.
  - The Steinberg sector `l^2_0(P^1(F_p))` is within `7 * 10^-4` of `2 sqrt 3` for
    `10^5 <= p <= 10^7`.
  - The whole group gives `3.52`--`3.55` for `31 <= p <= 211`.
  - The maximum over the principal-series sectors has excess `0.057`, `0.060` and
    `0.024` at `p = 1009`, `3001` and `10007`.  The share of sectors more than
    `0.01` above the edge falls from 5.5% to 1.5%.
  - The outliers are spread over characters of many orders, consistent with
    Tracy--Widom finite-size maxima.
  - Weak evidence for the principal-series part.  Cuspidal sectors were not
    computed separately at large `p`.  A proof or refutation is not in sight.
* **Localized outliers.**  Impossible in the limit.  The local limits of the
  Schreier graphs at special points (cusps, rational points) are quasi-regular
  representations with amenable stabilizers, which are weakly contained in
  `lambda_F`.  An outlier would have to be delocalized.
