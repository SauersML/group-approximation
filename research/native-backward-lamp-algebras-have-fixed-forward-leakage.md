---
rg: 2
id: native-backward-lamp-algebras-have-fixed-forward-leakage
kind: claim
title: Native backward S3 windows are finite but have forward Haar leakage at least five sixths
distinct_from:
  native-s3-algebra-enlargement-obstructs-scalar-commutants: That gives a conditional commutant obstruction from three algebra enlargement properties; this proves that every canonical finite backward-lamp window meets the first two properties and fails the third by a fixed bound.
artifacts:
  - research/artifacts/leavitt-backward-lamp-windows-and-canonical-haar-obstruction-2026-09-08.md
---

Use the native Leavitt compressor `u`, complementary subgroup `K`,
rank-three subgroup `L`, and `F_0=<k_+,k_->≅S_3`. Put

```text
F_j=u^(-j) F_0 u^j,
G_m=<F_0,...,F_m>,        G_infinity=union_(m>=0) G_m.
```

Every `G_m` embeds in `GL_(4^(m+1))(F_2)` through the complete
prefix code `{000,001,01,1}`. In particular `G_infinity` is locally
finite. The subgroup `<u,G_infinity>` is locally-finite-by-infinite-cyclic
and is amenable.

In the canonical group von Neumann algebra of `H`, let
`A_m=C[G_m]` and `B_m=u A_m u^(-1)`. With normalized canonical
trace, normalized Haar measure, and trace-preserving expectation,

```text
integral_(v in U(A_m)) ||v-E_(B_m)(v)||_2^2 dv
 =1-|G_m intersect uG_m u^(-1)|/|G_m|
 >=5/6.                                                   (1)
```

The algebras `A_m` contain `F_0` and commute exactly with `L`.
Thus this particular finite-subgroup enlargement has exact capture
and centralization, but cannot supply vanishing forward Haar leakage.
Local finiteness and amenability do not remove (1).

For each fixed `m`, (1) transfers to exact matrix representations
of `G_m` approximating its canonical native word evaluations, with
the same native matrix for `u`. Given such fixed-stage exactifications,
a sufficiently slow diagonal `m(n)->infinity` retains the first two
enlargement limits and has forward leakage with liminf at least `5/6`.
No uniform assertion for arbitrary growing windows follows from
fixed-word microstate convergence alone.

This excludes the stated canonical backward-window construction,
not all finite-dimensional algebra enlargements. It neither proves
nor disproves hyperlinearity. This is a written proof, not a new
Lean verification.

DERIVATION
prefix-windows-and-six-cosets-bound-native-haar-leakage
