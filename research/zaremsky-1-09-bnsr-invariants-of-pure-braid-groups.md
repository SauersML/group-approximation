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

The problem splits into three ranges, each a part-claim required by the answer
route:

- `m = 1`: computed by Koban, McCammond and Meier (arXiv:1306.4046,
  Theorem A): the complement of `Sigma^1(P_n)` is the union of the
  `binom(n,3) + binom(n,4)` "P_3-circles" and "P_4-circles".
- `m >= n - 2`: Zaremsky (arXiv:1507.08597, Theorem 3.9) proved
  `Sigma^{n-2}(P_n) = Sigma^infinity(P_n)` but recorded (p. 2) that "even the
  problem of fully computing `Sigma^2(P_4)` (which equals `Sigma^infinity(P_4)`)
  remains open".
- `2 <= m <= n - 3` (so `n >= 5`): only separation is known (Zaremsky,
  arXiv:1507.08597, Theorem 5.7: the characters `chi_n^m` lie in
  `Sigma^{m-3}(P_n)` but not in `Sigma^{m-2}(P_n)`).

## Attempts

- 2026-09-13, lane z1-09-pure-braid: Euler characteristic obstruction for the
  top range. `P_n` is `H x Z` with `H = P_n / Z(P_n)`, the pure mapping class
  group of the (n+1)-punctured sphere, which has a finite classifying space of
  dimension `n - 2` and Euler characteristic `(-1)^n (n-2)! != 0`. A nonzero
  Euler characteristic forces the characteristic varieties in degrees
  `<= n - 2` to cover the whole character torus, so Suciu's tropical bound
  (arXiv:2010.07499, Theorem 1.1) empties `Sigma^{n-2}(H, Z)`. With the split
  projection `P_n -> H` and "center survives" this should give
  `Sigma^m(P_n) = {[chi] : chi(Delta^2) != 0}` for all `m >= n - 2`. Being
  written up as its own claim.
- Middle range: split epimorphisms from `P_n` onto products of pure mapping
  class groups of punctured spheres with nonzero Euler characteristic give
  explicit characters outside `Sigma^m(P_n)`. Whether these exhaust the
  complement is the open question.
