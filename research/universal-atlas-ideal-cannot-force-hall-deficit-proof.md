---
rg: 2
id: universal-atlas-ideal-cannot-force-hall-deficit-proof
kind: route
title: Evaluate a putative ideal certificate in the exact Leavitt group factor
requires:
  - leavitt-factor-regular-charts-inner-conjugate
  - regular-chart-wedderburn-coefficient-compiler
target: universal-atlas-ideal-cannot-force-hall-deficit
---

Assume toward contradiction that such a graph `E` and ideal certificates
exist.  Let `S` be a source set with positive weighted Hall deficit and put

```text
P = sum_(v in S) p_v,
Q = sum_(u in N_E(S)) p_u.
```

By the regular-chart trace formula,

```text
gamma = tau(P)-tau(Q) > 0.                              (UIH1)
```

Use `leavitt-factor-regular-charts-inner-conjugate` to evaluate the relative
unitary variable at an internal unitary `W in L(Q_group)` which conjugates the
two labelled `A_8` chart embeddings in the exact group von Neumann algebra.
Every genuine atlas relator holds exactly there, so every compiled residual
`R_j(W)` is zero.  An algebraic two-sided `*`-ideal identity therefore forces

```text
p_u W p_v = 0            for every (v,u) notin E.       (UIH2)
```

Summing the orthogonal Fourier corners gives

```text
(1-Q) W P = 0.                                           (UIH3)
```

But the weighted Hall leakage estimate is not a matrix-only fact.  In any
finite tracial von Neumann algebra, for projections `P,Q` and a unitary `W`,

```text
||(1-Q) W P||_2^2
 = tau(P) - ||Q W P||_2^2
 >= tau(P)-tau(Q).                                      (UIH4)
```

Indeed `Q W P W^* Q <= Q`, so
`||QWP||_2^2 = tau(Q W P W^* Q) <= tau(Q)`.  Combining `(UIH1)`, `(UIH3)`
and `(UIH4)` gives

```text
0 >= gamma > 0,
```

a contradiction.

Nothing in the argument depends on a degree bound or on the number of
multipliers in a certificate.  Thus increasing the search degree in the free
`*`-algebra cannot evade the obstruction.  What must change is the **kind of
certificate**: it has to use finite-coordinate multiplicity/rank information
which disappears in the exact infinite-multiplicity factor model.