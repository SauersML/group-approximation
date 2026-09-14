---
rg: 2
id: separated-small-pairing-families-defeat-the-noise-test
kind: claim
title: Every separated pairing family of subexponential size defeats the folded long-code noise test
invalidates:
  - ugc-via-subexponential-pairing-enrichment
distinct_from:
  affine-long-code-test-has-no-uniform-soundness: that is the explicit algebraic instance for the affine family F_lin, built from a finite field with the sharper source bound 2/sqrt(N); this is the theorem for every delta_0-separated family, with random source games and a McDiarmid pairing decoder.
  dummy-padding-cannot-beat-the-random-guessing-floor: that bounds a decoding list proportional to the alphabet against the random-assignment floor; this constructs low-value source games whose noise-test outputs have value near one.
artifacts:
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
---

**ESTABLISHED.** Let `N = 2n >= 4`, `m >= 2`, `0 < rho < 1`,
`0 < delta_0 <= 1`, and let `P` be a family of perfect pairings of `[N]` in
which any two distinct pairings share at most a `1-delta_0` fraction of their
pairs. There is a `P`-rich 2-to-1 game `G` (every left vertex sees the uniform
distribution on `P`) with

```text
val(G) <= 16/N + (4 + 4 log_2 N + log_2 |P|) / |P|,
val(R_(rho,m)(G)) >= 1/m + (1-1/m) rho^3 - 2 |P| exp(-N rho^4 delta_0^2 / 96),
```

where `R_(rho,m)` is the folded long-code noise test of Braverman--Khot--Minzer,
ITCS 2021, Section 5.

So whenever `|P|/log N -> infinity` and `log |P| <= (rho^4 delta_0^2/96 - c) N`,
source value tends to zero while output value stays at least `rho^3 - o(1)`,
for every output alphabet. This generalizes the affine obstruction from
`F_lin` to any separated family. It covers fixed-point-free affine involutions
(`delta_0 = 1/2`, at most `2^(k^2+k)` members) and polynomial involutions of
bounded degree. Before this test can be applied, the pairing distribution at a
left vertex must be spread over exponentially many well-separated pairings.

Scope: the families of BKM's "Making games richer?" chain may still be small,
provided the test is applied only to fully rich instances. Families with many
near-duplicate pairings are not covered. No hardness, algorithm, or status of
UGC is asserted.
