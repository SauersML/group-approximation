---
rg: 2
id: affine-scaling-hnn-groups-pairwise-nonisomorphic-proof
kind: route
title: Recover dilation from the characteristic affine module
target: affine-scaling-hnn-groups-pairwise-nonisomorphic
requires: []
artifacts:
  - non_mf_group_notes.tex
  - research/artifacts/scaling-family-invariants-audit-2026-08-30.md
---

## 1. Direct-limit normal form

The ascending HNN normal form identifies

```text
H_m ~= U_m semidirect (SL_3(Z) direct_product <t_m>),
U_m=Z[1/m]^3,
```

where `SL_3(Z)` acts in the standard way and `t_m` acts on `U_m` by
multiplication by `m`.  Indeed, the increasing union of the translation
subgroups in `t_m^(-k) B t_m^k` is
`union_(k>=0) m^(-k)Z^3=Z[1/m]^3`; the linear copy is fixed by `t_m`.

## 2. The translation module is characteristic

We first recall the standard elementary consequence of the Margulis normal
subgroup theorem: `SL_3(Z)` has no nontrivial abelian normal subgroup.
Such a subgroup would either be central or finite index; the center of
`SL_3(Z)` is trivial, while a finite-index abelian subgroup is impossible.

Let `A` be an abelian normal subgroup of `H_m`, and project it to

```text
Q_m=H_m/U_m ~= SL_3(Z) direct_product Z.
```

Its projection is abelian and normal.  Projecting once more to `SL_3(Z)`
and using the preceding paragraph shows that it is contained in the central
`Z` factor of `Q_m`.

Suppose some `a in A` projects to `t_m^k` with `k!=0`.  For every
`u in U_m`, normality gives

```text
[a,u]=(m^k-1)u in A intersect U_m.
```

Because `A` is abelian, `a` must commute with this element.  Applying the
same conjugation action once more gives

```text
(m^k-1)^2 u=0.
```

But `U_m` is nonzero and torsion-free, and `m^k!=1`; contradiction.  Hence
the projection of `A` to `Q_m` is trivial and `A<=U_m`.  Since `U_m` itself
is normal abelian, it is the unique largest normal abelian subgroup of
`H_m`, and therefore characteristic.

## 3. Recovering `m`

Let `Phi:H_m -> H_n` be an isomorphism.  Characteristicity gives an
additive-group isomorphism

```text
F=Phi|_(U_m):U_m -> U_n.
```

The center of
`Q_m ~= SL_3(Z) direct_product Z` is exactly its `Z` factor, because the
center of `SL_3(Z)` is trivial.  The isomorphism induced by `Phi` on the
quotients must therefore send the class of `t_m` to the class of
`t_n^(epsilon)`, where `epsilon in {1,-1}`.  A translation factor in a lift
acts trivially on the abelian group `U_n`, so intertwining conjugation gives,
for every `u in U_m`,

```text
F(m u)=n^epsilon F(u).
```

Since `F` is additive, its left side is also `m F(u)`.  Choose `u` with
`F(u)!=0`.  If `epsilon=1`, torsion-freeness gives `m=n`.  If
`epsilon=-1`, multiplying by `n` gives `(mn-1)F(u)=0`, impossible for
`m,n>=2`.  Thus an isomorphism forces `m=n`; the converse is tautological.

This also shows why the invariant is stronger than localization type:
`Z[1/m]^3` alone sees only the primes dividing `m`, while the characteristic
quotient action sees the exact integer, including prime exponents.
