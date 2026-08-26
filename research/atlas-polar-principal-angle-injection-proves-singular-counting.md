---
rg: 2
id: atlas-polar-principal-angle-injection-proves-singular-counting
kind: route
title: Inject the Atlas source into the twelve polar residual high spaces
target: atlas-six-row-singular-counting-dominates-nontrivial-s3
requires:
  - atlas-six-row-polar-high-spaces-meet-source-at-acute-angle
---

Fix `U,t` and use `(PAI1)--(PAI2)`.  Condition `(PAI3)` says that the
orthogonal projection

```text
Z_t : Ran(P_t) -> Ran(Z_t)
```

is injective.  Therefore

```text
rank(P_t)
 <=rank(Z_t)
 <=sum_r (rank(Q_(r,t))+rank(Q'_(r,t)))
 =2 sum_r rank(Q_(r,t)).                              (PPI1)
```

Divide by the ambient dimension.  Since

```text
tr(Q_(r,t))=N_(R_r)(kappa t),
```

equation `(PPI1)` is `(SCI3)` with the explicit constant

```text
C_rank=2.                                            (PPI2)
```

The proof is purely finite-dimensional and uses only polar decomposition,
principal angles, and integer rank.  It does not assert an operator
domination and therefore does not extend formally to the exact Leavitt
factor.


