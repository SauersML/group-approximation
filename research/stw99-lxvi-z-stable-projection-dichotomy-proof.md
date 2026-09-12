---
rg: 2
id: stw99-lxvi-z-stable-projection-dichotomy-proof
kind: route
title: Compare a full finite projection with the properly infinite unit
target: stw99-lxvi-z-stability-forbids-mixed-projections
requires:
  - stw74-simple-infinite-projections-are-properly-infinite
artifacts:
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

Rordam's Theorem 4.5 in
[*The stable and the real rank of Z-absorbing C*-algebras*](https://arxiv.org/abs/math/0408020)
shows that `Cu(B)` is almost unperforated.

Suppose first that `B` contains an infinite projection.  Since `B` is simple,
that projection is properly infinite by
`stw74-simple-infinite-projections-are-properly-infinite`.  Its infiniteness
also makes the unit infinite: adjoining its complementary projection to a
proper equivalent subprojection produces a proper subprojection equivalent
to the unit.  Applying the same theorem once more, put

```text
u=[1_B],                 2u=u.
```

The properly infinite unit is the largest element of `Cu(B)`.  Indeed every
finite-matrix unit is a finite multiple of `u`, hence equals `u`, and every
stabilized positive class is the supremum of cutdowns dominated by such
matrix units.

Assume toward a contradiction that `0!=p in B` is finite, and write
`x=[p]`.  Simplicity makes `p` full.  Compactness of the unit class therefore
gives `u<=n x` for some finite `n`.  Since `x<=u` and `n u=u`, one has

```text
n x=u.                                                   (1)
```

Proper infiniteness and (1) now give

```text
(n+1)u=u=n x.
```

Almost unperforation yields `u<=x`; the reverse inequality was already
known, so `x=u`.  Cuntz equivalence of projections is Murray--von Neumann
equivalence.  Hence `p` is equivalent to the properly infinite unit and is
itself properly infinite, contradicting finiteness.  Thus the infinite
regime contains no nonzero finite projection, and every nonzero projection
is properly infinite by simplicity.

It remains to identify the other regime as stable finiteness.  Suppose the
unit of `B` is finite.  If some matrix algebra `M_m(B)` contained an infinite
projection, then the preceding mixed-projection argument, applied to the
simple Z-stable algebra `M_m(B)`, would forbid its finite projection
`e_11 tensor 1_B`.  That projection is Murray--von Neumann equivalent to the
finite projection `1_B`, so this is impossible.  Hence every matrix algebra
over `B` is finite, proving stable finiteness and the dichotomy.

An LXVI witness contains both kinds of projection and is therefore not
Z-stable.  Finally, a separable simple unital algebra of finite nuclear
dimension is either elementary or Z-stable by Winter's theorem
([*Nuclear dimension and Z-stability of pure C*-algebras*](https://arxiv.org/abs/1006.2731)).
The elementary case is a matrix algebra and cannot contain an infinite
projection.  Thus no separable mixed algebra has finite nuclear dimension,
which proves the last assertions.
