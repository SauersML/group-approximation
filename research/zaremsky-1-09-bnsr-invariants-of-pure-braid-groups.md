---
rg: 2
id: zaremsky-1-09-bnsr-invariants-of-pure-braid-groups
kind: claim
title: "Zaremsky Problem 1.9 resolved: compute the BNSR invariants of the pure braid groups"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 9,
verbatim: "Compute the BNSR-invariants of pure braid groups."

This claim is the question. It is established only through the answer route
`zaremsky-1-09-by-computation`, which requires one part-claim per range of
the pair `(n, m)`. Never write a `requires: []` route into this claim.

## Precise reading

`P_n` is the pure braid group on `n` strands. Its character sphere `S(P_n)`
has dimension `binom(n,2) - 1`; a character is `chi = sum_{i<j} a_{ij} omega_{ij}`
where `omega_{ij}` is the winding-number character of strands `i` and `j`
(Zaremsky, arXiv:1507.08597, Section 3.1). "Compute" means: for every `n` and
every `m` in `{1, 2, ..., infinity}`, give an explicit description of the
subset `Sigma^m(P_n)` of `S(P_n)` (equivalently of its complement) in terms of
the coefficients `a_{ij}`. Since `P_n` has a finite classifying space, every
`Sigma^m(P_n)` is defined.

The three ranges, each a part-claim required by the answer route:

- `m = 1`: `pure-braid-bns-invariant-is-circle-complement`
  (Koban–McCammond–Meier, arXiv:1306.4046, Theorem A; imported).
- `m >= n - 2`: `pure-braid-top-bnsr-invariants-are-center-nonvanishing`,
  `Sigma^m(P_n) = {chi : sum a_{ij} != 0}` (landed 2026-09-13, unreviewed). This
  includes `Sigma^2(P_4)`, which Zaremsky (arXiv:1507.08597, p. 2) recorded as
  open, so all invariants are computed for `n <= 4`.
- `2 <= m <= n - 3` (so `n >= 5`): `pure-braid-middle-bnsr-invariants-computed`,
  OPEN. Known: separation (Zaremsky, Theorem 5.7), block-supported zero-sum
  characters outside `Sigma^D` (`pure-braid-product-projections-obstruct-bnsr-invariants`),
  the resonance upper bound (`arrangement-bnsr-invariants-avoid-real-resonance`),
  and Zaremsky's Proposition 5.6 region inside `Sigma^{n-3}`.

## Attempts

- 2026-09-13, lane z1-09-pure-braid: top range settled by the Euler
  characteristic of `H_n = P_n/Z(P_n)` (`(-1)^n (n-2)!`, aspherical of dimension
  `n-2`) through Suciu's tropical bound and Meinert's split-epimorphism
  corollary; artifact `research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md`.
- Middle range: conjecture that `Sigma^m(P_n)` is the complement of the real
  resonance variety `R^{<=m}(P_n)` in every degree
  (`pure-braid-bnsr-complements-are-real-resonance-varieties`; true for `m = 1`
  and `m >= n - 2`), plus an explicit computation of the higher resonance
  varieties (`braid-arrangement-higher-resonance-varieties-computed`). Smallest
  open case `Sigma^2(P_5)`; artifact
  `research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md`.
