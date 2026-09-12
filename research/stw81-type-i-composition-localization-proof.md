---
rg: 2
id: stw81-type-i-composition-localization-proof
kind: route
title: Test every type-I composition stratum by a rank-one hereditary shadow
target: stw81-type-i-topological-dimension-collapse
requires: []
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Choose a composition series `(J_alpha)` for the separable type-I algebra
`A` whose nonzero successive factors

```text
D_alpha = J_(alpha+1)/J_alpha
```

have continuous trace.  Each `D_alpha` is an ideal in the quotient
`A/J_alpha`.  A hereditary subalgebra of `D_alpha` is therefore hereditary
in `A/J_alpha`.

Fix a point of `Prim(D_alpha)`.  Local triviality supplies an open
neighborhood `U` and a rank-one corner `C_0(U)e ~= C_0(U)` inside
`D_alpha`.  This is one of the commutative hereditary subalgebras quantified
over by the hypothesis on `A`, so `dim(U)<=1`.  Locality of covering
dimension gives

```text
dim(Prim(D_alpha)) <= 1
```

for every continuous-trace factor.

Brown--Pedersen topological dimension for a type-I algebra is the supremum
of the covering dimensions of the locally closed Hausdorff strata in such a
composition series.  Hence `topdim(A)<=1`.

If `A` were a counterexample to Problem LXXXI, its nuclear dimension would
be a finite integer at least two, producing the asserted strict separation.

**Trust boundary.**  The route uses the standard continuous-trace
composition series for separable type-I algebras and the composition-series
description of Brown--Pedersen topological dimension.  It does not import or
assume an inequality between topological and nuclear dimension; establishing
that inequality at dimension one is precisely the remaining type-I hinge.
