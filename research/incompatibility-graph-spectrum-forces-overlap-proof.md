---
rg: 2
id: incompatibility-graph-spectrum-forces-overlap-proof
kind: route
title: Order the adjacency matrix below by its Perron and least eigenvalues, then Cauchy-Schwarz
target: incompatibility-graph-spectrum-forces-overlap
requires: []
---

Let `G_ij = tau(Q_i Q_j)`.  The matrix `G` is the Gram matrix of `Q_1,...,Q_m`
in `L^2(M,tau)` and is therefore positive semidefinite, with `G_ii = tau(Q_i) =
beta`.  Note

```text
sum_({i,j} in E) tau(Q_i Q_j) = (1/2) <A, G>,
```

where `<A,G> = sum_(i,j) A_ij G_ij` and `A` has zero diagonal.

**Ordering the adjacency matrix.**  Because `G` is `r`-regular, the all-ones
vector is an eigenvector of `A` with eigenvalue `r`, and on its orthogonal
complement `A >= lambda_min`.  Writing `J` for the all-ones matrix, this is
exactly

```text
A >= (r/m) J + lambda_min ( I - J/m ).
```

Pairing with the positive semidefinite `G` preserves the inequality:

```text
<A,G> >= (r - lambda_min)/m . <J,G> + lambda_min <I,G>.
```

**Evaluating the two pairings.**  `<I,G> = sum_i tau(Q_i) = m beta`.  For the
other, put `S = sum_i Q_i`; then `<J,G> = sum_(i,j) tau(Q_i Q_j) = tau(S^2)`,
and Cauchy--Schwarz for the trace state gives

```text
tau(S^2) >= tau(S)^2 = (m beta)^2.
```

Since `r - lambda_min > 0` for any graph with an edge, we may substitute the
lower bound:

```text
<A,G> >= ((r - lambda_min)/m)(m beta)^2 + lambda_min m beta
       = m beta^2 (r - lambda_min) + lambda_min m beta
       = m beta ( r beta + lambda_min (1 - beta) ).
```

Halving gives `(IGS1)`.

**Complete graph.**  `r = m-1`, `lambda_min = -1`, so
`r beta + lambda_min(1-beta) = (m-1)beta - 1 + beta = m beta - 1`, which is
`(IGS2)`.  `(IGS3)` substitutes `beta = 3/7`, `m = 3` from `(MSD1)` of
`marked-hs-separation-forces-spectral-density`.
