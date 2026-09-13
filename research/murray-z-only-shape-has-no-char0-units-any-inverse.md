---
rg: 2
id: murray-z-only-shape-has-no-char0-units-any-inverse
kind: claim
title: Every unit of K[P] of Murray's z-only shape is trivial in characteristic zero, whatever its inverse
distinct_from:
  murray-z-only-ansatz-has-no-char0-units: that assumes the inverse is given by Gardam's formula; this drops that assumption and covers every unit of the shape.
  promislow-symmetric-piece-units-satisfy-gardam-equations: that is the exact unit criterion for all elements with symmetric pieces over any domain; this applies it to Murray's shape in characteristic 0.
  rational-unit-conjecture-torsion-free: that is the unit conjecture over Q for every torsion-free group; this excludes one ansatz family on one group.
artifacts:
  - research/artifacts/promislow-reduced-norm-2026-09-13.md
---

**ESTABLISHED.** Let `K` be a field of characteristic 0, `f_1, ..., f_7` in
`K[z^(+-1)]`, and

    p = (1+x)(1+y) f_1
    q = (1+x)(x^-1+y^-1) f_2 + (1+y^-1) f_3
    r = (1+y^-1)(x+y) f_4 + (1+x) f_5
    s = (x+4+x^-1+y+y^-1) f_6 + f_7

This is Murray's ansatz (arXiv:2106.02147, Section 4), as recorded in
`murray-z-only-ansatz-has-no-char0-units`. Let `u = p + q a + r b + s ab`.

**Theorem.** If `u` is a unit of `K[P]`, then `f_1 = ... = f_6 = 0` and
`u = lambda z^k ab` for some `lambda in K^x` and `k in Z`. Nothing is assumed
about `u^-1`.

This strengthens `murray-z-only-ansatz-has-no-char0-units`, which assumes that
the inverse is Gardam's formula `u'`. The strengthening comes from
`promislow-symmetric-piece-units-satisfy-gardam-equations`: on this shape
every unit already has inverse `N^-1 u'`.

**Scope.** Only the `f_i` depending on `z` alone are covered. Other shapes are
not, including symmetric pieces with arbitrary `x`, `y`-dependence. Over `F_d`,
for odd primes `d`, Murray's Theorem 3 gives nontrivial units of this shape.

DERIVATION
[[murray-z-only-any-inverse-from-symmetric-pieces]]
