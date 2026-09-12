---
rg: 2
id: stw81-ctdim-extension-decomposition-proof
kind: route
title: Split every continuous-trace subquotient into ideal and quotient pieces
target: stw81-ctdim-extension-maximum
requires:
  - stw81-continuous-trace-shadow-invariant
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Continuous-trace subquotients of `I` and `D` are also subquotients of `E`:
for `I` this uses transitivity of the ideal relation, and for `D` one lifts
the two defining ideals through `E -> D`.  Therefore

```text
ctdim(E) >= max(ctdim(I),ctdim(D)).                 (1)
```

For the reverse inequality, fix a continuous-trace subquotient `C` of `E`.
Intersect the two ideals defining `C` with `I`, or equivalently apply the
standard induced-extension construction to that subquotient.  It gives an
exact sequence

```text
0 -> C_I -> C -> C_D -> 0,                         (2)
```

where `C_I` is a subquotient of `I` and `C_D` is a subquotient of `D`.
Ideals and quotients of continuous-trace algebras are continuous trace, so
both nonzero terms in (2) are among the algebras tested by `ctdim(I)` and
`ctdim(D)`.

Let `X=Prim(C)`.  The ideal `C_I` corresponds to an open subset `U` of `X`,
and `Prim(C_D)` is the closed complement `X\U`.  Since `C` is separable,
`X` is second countable and metrizable.  The open set `U` is an `F_sigma`
subset of `X`; write it as a countable union of closed subsets of dimension
at most `dim(U)`.  The countable closed-sum theorem for covering dimension
then gives

```text
dim(X) = max(dim(U),dim(X\U)).                      (3)
```

Equations (2)--(3) imply

```text
dim(Prim(C)) <= max(ctdim(I),ctdim(D)).
```

Taking the supremum over `C` and combining with (1) proves the formula.

**Trust boundary.**  The proof uses the standard ideal correspondence for
subquotients, permanence of continuous trace under ideals and quotients,
and the countable closed-sum theorem for covering dimension of metric
spaces.  It does not use the unresolved nuclear-dimension extension formula.
