---
rg: 2
id: affine-sl3-property-t-finite-index-proof
kind: route
title: Lift property (T) from the level-three congruence subgroup of finite index
target: affine-semidirect-sl3-source-has-property-t
requires:
  - affine-congruence-source-is-kazhdan
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

## Why sufficient

`Gamma(3) = ker(SL_3(Z) -> SL_3(Z/3))` has index `|SL_3(Z/3)|`, finite, in
`SL_3(Z)`.  The translation factor is the same on both sides, so

```text
P = Gamma(3) x| Z^3  <=  Z^3 x| SL_3(Z) = Gamma
```
has that same finite index.  The prerequisite establishes property (T)
for `P`.  Property (T) is inherited by finite-index **overgroups** as
well as by finite-index subgroups — it is a commensurability invariant —
so `Gamma` has property (T).  This is a genuine step and not a
restatement: the two groups are different, and the prerequisite is
deliberately about the torsion-free congruence subgroup, which does not
fix the three nested lattices used downstream.

## The independent citation check

The dossier this node ingests derives `(AT1)` from two published results
instead.  Recording the derivation so that the finite-index route can be
audited against it.

Ershov--Jaikin-Zapirain Theorem 1.1 gives property (T) for `EL_n(R)`,
`n >= 3`, over a finitely generated unital associative ring `R`.  At
`R = Z` this is `EL_3(Z)`, and `EL_3(Z) = SL_3(Z)` by Euclidean row
reduction: integer row additions reduce a primitive first column to a
coordinate vector, determinant-one signed interchanges are products of
elementary matrices, column additions clear the first row, and the
remaining `SL_2(Z)` block is reduced the same way.  Their Proposition
8.1, attributed to Kassabov, gives relative property (T) for
`((EL_p(R) x EL_q(R)) x| M_(pxq)(R), M_(pxq)(R))`; at `R = Z`, `p = 3`,
`q = 1` the second factor `EL_1(Z)` is trivial and the pair is
`(Gamma, Z^3)`.

Combination.  Let `pi` be a unitary representation of `Gamma` with almost
invariant unit vectors `xi_j`, and let `P_0` project onto the
`Z^3`-fixed subspace.  Normality of `Z^3` makes `P_0` commute with
`pi(Gamma)`.  On `(I - P_0)H` there are no `Z^3`-fixed vectors, so a
finite relative Kazhdan pair gives
`||(I - P_0) xi_j|| <= c max_(s in S) ||pi(s)xi_j - xi_j|| -> 0`.  Thus
`P_0 xi_j` has norm tending to one and gives almost invariant vectors for
a representation factoring through `SL_3(Z)`, whose property (T) supplies
a nonzero `Gamma`-fixed vector.  The finite-Kazhdan-pair formulation
follows from this almost-invariant-vector formulation by the usual
direct-sum contradiction.
