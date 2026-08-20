---
rg: 2
id: non-ce-bcs-has-robust-approximate-energy-gap-proof
kind: route
title: A vanishing approximate BCS energy would define a BCS representation in a tracial matrix ultraproduct
target: non-ce-bcs-has-robust-approximate-energy-gap
requires:
  - mipstar-bcs-tracial-nonru-exists
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

If no positive constant existed, choose dimensions `d_n` and unitary tuples
`Z_x^(n)` for which the left side of `(RFMG)` tends to zero.  Pass to the
tracial matrix ultraproduct and write
`Z_x=[Z_x^(n)]_omega`.

The square relators imply `Z_x^2=I` in the ultraproduct.  Since `Z_x` is
unitary, it is consequently a self-adjoint involution there.  Every context
commutator also vanishes, so the `Z_x` belonging to a common context commute
exactly.  Therefore the factors

```text
P_(x,a_x)=(I+(-1)^(a_x)Z_x)/2
```

are commuting projections there.  For every forbidden assignment, the class
of their fixed-order product has squared `L^2` norm equal to the ultralimit of
the corresponding summand in `(RFMG)`, hence is zero.  Thus every forbidden
joint spectral projection vanishes.

The tuple consequently satisfies the defining relations of the BCS algebra
and gives a unital representation into a tracial matrix ultraproduct.
Composing with its trace produces a Connes-embeddable tracial state on the BCS
algebra, contradicting `mipstar-bcs-tracial-nonru-exists`.  Hence a positive
`beta_B^rob` exists.

