---
rg: 2
id: iwahori-support-erasure-has-linear-commutator-leakage
kind: claim
title: Erasing a supplied positive-central support pays linear commutator leakage in the retained residual
distinct_from:
  approximate-central-tensor-coverage-forces-capture: that rounds a supplied large positive corner and assumes bounded-payload authentication for endpoint capture; this erases a supplied small positive-central support, keeps the negative sector, and bounds the remaining residual directly without payload or endpoint assumptions.
  iwahori-spectral-residual-gate-has-polynomial-step: that contracts under spectral and operator-residual hypotheses at the actual input; this is a preliminary exact support-erasure operation with a different explicit conditional contraction budget and supplies no spectral projection satisfying that budget.
  modular-multiplicities-reconcile-at-quadratic-rank-cost: that reconciles two supplied exact endpoints by changing central signs and spectral labels; this uses one supplied projection at one pair and preserves the original common central involution.
artifacts:
  - research/artifacts/iwahori-support-erasure-and-linear-leakage-2026-09-08.md
---

Let `U=(S_1,B_1,S_2,B_2)` be an exact modular vertex pair on
`C^n` with common central involution
`S_i^2=B_i^3=Z`. Let `P` be a supplied projection with `ZP=P`,
put `Q=I-P`, and define

```text
alpha=rank(P)/n,
kappa_2=max_g ||[U_g,P]||_2,
kappa_inf=max_g ||[U_g,P]||_op.
```

Here matrix HS norms are normalized on the full original dimension,
and `g` ranges over the four vertex generators. For residual rows
`R_a(U)=w_(a,1)(U)-w_(a,2)(U)`, let `L` be the maximum sum of
the two word lengths. There is an exact vertex pair `U_hat` in the
same dimension with the same common central involution, such that
`U_hat_g P=P`, and simultaneously

```text
max_g rank(U_hat_g-U_g)/n <= 3alpha,
max_g ||U_hat_g-U_g||_2
    <= min(2sqrt(3alpha), 4kappa_2+2sqrt(alpha)),
R_a(U_hat)=Q R_a(U_hat) Q,
||R_a(U_hat)-Q R_a(U) Q||_2 <= 4L kappa_2,
||R_a(U_hat)-Q R_a(U) Q||_op <= 6L kappa_inf.          (SEL1)
```

In particular put `e=max_a ||R_a(U)||_2` and
`h=max_a ||Q R_a(U)Q||_2`. Whenever the supplied projection obeys

```text
h+4L kappa_2 <= e/2,                                 (SEL2)
```

this operation is a same-dimensional half-contraction. If additionally
`alpha<=B e`, its generator movement is at most `2sqrt(3B e)`.
The retained operator residual is at most
`max_a ||Q R_a(U)Q||_op+6L kappa_inf`.

No projection meeting these budgets is constructed here. Rank or
residual support alone does not establish `(SEL2)`. The negative
central sector is retained exactly; only the supplied positive-central
block is replaced by trivial representations. There is no
commutator-only bound for this replacement's generator movement,
and no conclusion of global strict or flexible stability.
