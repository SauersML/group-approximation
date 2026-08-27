---
rg: 2
id: non-mf-groups-with-free-integral-representation-geometry
kind: claim
title: Non-MF groups can have the integral representation geometry of free groups
root: true
artifacts:
  - research/non-mf-free-integral-representation-geometry-proof.md
distinct_from:
  mf-camouflage-preserves-integral-representation-geometry: that treats an arbitrary finitely presented MF quotient; this specialization makes every representation scheme explicit and proves smoothness and unobstructedness in all ranks.
---

For every integer `r>=0` there is a finitely presented non-MF group `Gamma_r`
such that, for every commutative ring `A`, its representations on finitely
presented `A`-modules are exactly finitely presented modules equipped with
`r` arbitrary automorphisms.

Equivalently, for every `n>=1`, there is an isomorphism of affine schemes over
the integers

```text
Rep_n(Gamma_r) ~= GL_n^r.                            (FRG1)
```

These isomorphisms are compatible with conjugation.  Hence:

1. every `Rep_n(Gamma_r)` is smooth over `Z`, with geometrically integral
   fibers and relative dimension `r*n^2`;
2. every framed finite-dimensional representation of `Gamma_r` has
   unobstructed infinitesimal deformation theory;
3. the character stack is `[GL_n^r/GL_n]`, exactly as for the free group
   `F_r`;
4. over every field, `Gamma_r` and `F_r` have the same proalgebraic
   completion and the same finite-dual Hopf algebra.

For `r=0`, `(FRG1)` is `Spec(Z)`: there is a nontrivial finitely presented
group whose only representation in `GL_n(A)` is the trivial one, for every
commutative ring `A` and every `n`.  For `r>=1`, the quotient onto `F_r`
splits, but its nontrivial one-word kernel is invisible to all of the
representation geometry above.

Thus even smooth, geometrically integral, everywhere-unobstructed integral
representation schemes in every rank do not imply MF.
