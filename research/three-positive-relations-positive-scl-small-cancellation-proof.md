---
rg: 2
id: three-positive-relations-positive-scl-small-cancellation-proof
kind: route
title: Certify a C'(1/6) presentation carrying the three positive relations, then apply Calegari--Fujiwara
target: three-positive-relations-allow-positive-scl
requires:
  - cprime-one-sixth-presentations-hyperbolic-and-torsion-free
  - calegari-fujiwara-gap-theorem-strong-version
artifacts:
  - research/artifacts/hl-zd-amplification-2026-09-13.md
---

(1) **Shapes.** `sc_verify.py` asserts: `R_1` uses only the letters `x, y`; `R_2` uses only
`x, Y`, and every `Y` is followed cyclically by `x`, so `R_2` is a product of the tokens
`x` and `Yx = y^-1 x`; `R_3` uses only `y, X`, and every `X` is followed by `y`, so `R_3`
is a product of `y` and `Xy = x^-1 y`. In each relator both tokens occur. The inverse of
`R_1` is a positive word in `x^-1, y^-1` using both. This gives item 1.

(2) **Small cancellation.** Both programs work over exact integers on MSI (artifact
directory `research/artifacts/hl-zd-amplification-2026-09-13/`).
- `sc_verify.py` (md5 `0e9fa7497c3e53a27ba49069318505f2`) builds all cyclic conjugates of
  the relators and their inverses (`632` words), checks they are pairwise distinct and that
  no relator is a proper power, and computes the longest common prefix of every ordered
  pair: largest piece-over-length ratio `1/7` (output `verify3.txt`).
- `sc_verify_hash.py` (md5 `8487a56d3e2edddb035d40a146065e86`) indexes every cyclic subword
  by position and finds longest pieces `11`, `17`, `17` in relators of lengths `77`, `120`,
  `119`; no piece of length `18` exists (output `verify3_hash.txt`).
All relators are cyclically reduced (asserted). So `<x, y | R_1, R_2, R_3>` satisfies
classical `C'(1/6)` with no proper-power relator, and by
`cprime-one-sixth-presentations-hyperbolic-and-torsion-free` the group `G` is torsion-free,
word-hyperbolic, and its presentation complex `K` is aspherical.

(3) **Homology.** The exponent sums of `(x, y)` in `R_1, R_2, R_3` are `(38, 39)`,
`(79, -41)`, `(-37, 82)` (computed in `verify3.txt`). The `2 x 2` minors are `-4639`,
`4559`, `4961`, with `gcd = 1`, so `H_1(G; Z) = Z^2 / <rows> = 0`. Since `K` is a
`K(G, 1)` with one vertex, two edges and three faces, `1 - b_1 + b_2 = chi(K) = 2`, so
`b_2(G) = 1` and `G != 1`.

(4) **Nontriviality.** Token counts: `R_2` has `38` tokens `x` and `41` tokens `y^-1 x`;
`R_3` has `45` tokens `y` and `37` tokens `x^-1 y`.
- If `x = 1`, then `R_2 = y^-41 = 1`, so `y = 1` (torsion-free) and `G = 1`.
- If `y = 1`, then `R_3 = x^-37 = 1`, so `x = 1` and `G = 1`.
- If `x^-1 y = 1`, then `R_1 = x^77 = 1`, so `x = 1` and `G = 1`.
Each contradicts (3).

(5) **Quasimorphisms.** By `calegari-fujiwara-gap-theorem-strong-version` there are
homogeneous quasimorphisms `h_1, h_2, h_3` with `h_1(x) = 1`, `h_2(y) = 1`,
`h_3(x^-1 y) = 1`. For real `t`, `phi_t = h_1 + t h_2 + t^2 h_3` is a homogeneous
quasimorphism. Now `phi_t(x) = 1 + t h_2(x) + t^2 h_3(x)`,
`phi_t(y) = h_1(y) + t + t^2 h_3(y)` and `phi_t(x^-1 y) = h_1(x^-1 y) + t h_2(x^-1 y) + t^2`
are nonzero polynomials in `t` (constant, linear and quadratic coefficients `1`), so
all but finitely many `t` make all three values nonzero.

(6) **scl.** `H_1(G; Z) = 0` gives `G = [G, G]`, and the consequence of
`calegari-fujiwara-gap-theorem-strong-version` gives positive scl for each of the three
elements. The upper bound `5/6` is consequence 1 of
`support-three-zero-divisor-quasimorphism-bound-five-thirds`, whose proof uses only the
relations of item 1.

(7) **Barrier.** The routes `support-three-zero-divisor-quasimorphism-bound-proof` and
`support-three-quasimorphism-five-thirds-proof` require only
`zero-divisor-support-vertex-cones-contain-positive-relations`, and use of it only
consequence 4, which item 1 realizes in `G`. A deduction of `phi(x) = 0` from those inputs
would give it in `G`, contradicting (5).
