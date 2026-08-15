---
rg: 2
id: abelian-lamp-mf-classification-proof
kind: route
title: Additive character ramps upward, spectral collapse downward
target: abelian-lamp-mf-classification
requires: [zero-dimensional-spectral-collapse]
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

## Why sufficient

**Torsion-free direction.**  `A` embeds in `A tensor_Z Q`, a countable
`Q`-vector space; choosing a basis inside a complement of `Q (2 pi)` in
`R` (over `Q`) gives an additive `theta : A -> R` with
`exp(i theta(a)) != 1` for every `a != 0`.  Run the construction of
`infinite-cyclic-compression-lamp-mf-proof` with the root lamp `a`
represented by the diagonal `delta_y -> exp(i theta(a) f_n(y)) delta_y`.
Additivity of `theta` makes this an exact representation of all of `A`,
not only of one cyclic generator; covariance, exact commutation of
separated sites, and the two detection estimates are verbatim as there,
with the bump-center value `exp(i theta(a_{j_0})) != 1`.

**Torsion direction.**  Let `a in A` have finite order `m > 1` and let
`c_a` be the lamp `a` at the root site.  In every corona representation
`pi` of `A^(X) semidirect H`: the image `pi(c_a)` has order dividing `m`,
so its spectrum lies in the finite set `mu_m` — zero-dimensional; `c_a`
is centralized by `L_1 = t L t^{-1}` (the root stabilizer contains
`L_1`); and its `L`-conjugates are lamps, which commute.
`zero-dimensional-spectral-collapse` forces
`pi(g c_a g^{-1}) = pi(c_a)` for every `g in L`.  Choosing
`g in L \ L_1` makes `g c_a g^{-1} c_a^{-1}` a nontrivial two-site lamp
configuration killed by every corona representation, so the group is not
MF.
