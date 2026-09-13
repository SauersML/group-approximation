---
rg: 2
id: zaremsky-1-24-houghton-dehn-function
kind: claim
title: "Zaremsky Problem 1.24 resolved: is the Dehn function of Houghton's group H_n (n >= 3) polynomial, and is it quadratic?"
root: true
distinct_from:
  houghton-carmichael-sections-have-unbounded-edge-area: that shows one specific family of Carmichael relators in H_k has unbounded van Kampen area, a statement about areas of fixed relation shapes with growing conjugators; this is the question of the growth type of the Dehn function of H_n as a function of word length.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 24
(added 2/24/26), verbatim: "For n ≥ 3, Houghton's group H_n is finitely
presented. Lee proved the Dehn function of H_n is at most exponential. Is it
polynomial? Quadratic?"

This claim is the question. It is established only through an answer route:

- **Quadratic** (both answers yes): `zaremsky-1-24-by-quadratic` requires
  `houghton-groups-have-quadratic-dehn-function`.
- **Polynomial but not quadratic**: `zaremsky-1-24-by-polynomial-not-quadratic`
  requires `houghton-groups-have-polynomial-dehn-function` and
  `some-houghton-group-has-superquadratic-dehn-function`.
- **Not polynomial**: `zaremsky-1-24-by-superpolynomial` requires
  `some-houghton-group-has-superpolynomial-dehn-function`.

Never write a `requires: []` route into this claim. If the answer depends on
`n` (for example quadratic for large `n` and not for `n = 3`), the per-`n`
statements are recorded as separate claims and a mixed answer route is added
here with its own justification.

**Reading.** `H_n` is the group of permutations of `Y_n = {1,...,n} x N`
that agree with a translation `(j,p) -> (j, p + t_j)` on each ray outside a
finite set. The translation vector gives `1 -> Sym_fin(Y_n) -> H_n -> Z^(n-1) -> 1`.
The Dehn function is taken for any finite presentation; its `≃`-class does not
depend on the presentation. "Polynomial" means `δ(x) ≼ x^d` for some `d`;
"quadratic" means `δ(x) ≃ x^2`.

**Known bounds.**

- Upper: `houghton-groups-have-at-most-exponential-dehn-function`
  (S. R. Lee, arXiv:1212.0257, Theorem D).
- Lower: `houghton-groups-have-at-least-quadratic-dehn-function`
  (`H_n` is not hyperbolic, and Gromov's gap theorem).
- Word length: Burillo, Cleary, Martino and Röver (arXiv:1403.0026,
  Theorem 4.1) show `P/C <= |σ| <= K P log P` for `n >= 3`, where
  `P(σ)` is the complexity (the sum over rays of the largest index where
  `σ` deviates from its eventual translation). So finitary permutations are
  not exponentially distorted.
- `H_n` contains no Baumslag–Solitar subgroup `BS(1,m)` with `|m| >= 2`:
  if `t a t^(-1) = a^m` then the translation vectors satisfy
  `v(a) = m v(a)`, so `v(a) = 0` and `a` is a finitary permutation, which has
  finite order. The usual source of exponential area is absent.

## Attempts

- 2026-09-13 (z1-24-houghton): reduction of the Dehn function to the area
  of commutation relations among far-apart transpositions, and a search for
  cheap commuting transporters (translations along lines that avoid a given
  finite set). Work in progress in `research/artifacts/zp-houghton-dehn-2026-09-13*.md`.
