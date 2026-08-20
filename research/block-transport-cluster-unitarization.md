---
rg: 2
id: block-transport-cluster-unitarization
kind: claim
title: Small off-cluster unitary mass rounds to stabilized clusterwise unitaries
---

Let `rho,sigma:H->U(d)` be exact finite-dimensional unitary representations,
let `(P_i)_(i in I)` and `(Q_j)_(j in J)` be finite orthogonal decompositions
of `1` by projections reducing `rho` and `sigma`, and let `U in U(d)`.
Choose a bipartite graph `G subset I x J`.  Its connected components `C`
determine reducing projections

```text
P_C = sum_(i in C) P_i,       Q_C = sum_(j in C) Q_j.
```

Put

```text
gamma = sum_((i,j) notin same G-component) ||P_i U Q_j||_2^2.
```

Then one can add at most `gamma d` dimensions to each side, carrying trivial
representations, and obtain orthogonal stabilized component decompositions of
equal dimensions together with unitaries `W_C` between corresponding
components.  For `W=directSum_C W_C`, normalized relative to the original
`d`,

```text
||W-U||_2 <= (1+sqrt(2)) sqrt(gamma),                 (BCU1)
```

where `U` is extended by zero on the added coordinates before the comparison.
Moreover, if

```text
E(U)=sum_(s in S)||rho(s)U-U sigma(s)||_2^2
```

for a finite `S subset H`, and the added coordinates carry the trivial
representation on both sides, then

```text
sqrt(E(W)) <= sqrt(E(U)) + 2 sqrt(2 |S| gamma).        (BCU2)
```

In particular, if `E(U)->0` and `gamma->0`, the original almost intertwiner
can be replaced, after `o(d)` stabilization, by an almost intertwining unitary
which **never mixes different connected components of `G`**.

No bounded degree, singular-value lower bound, or Hall hypothesis is required.
The statement does not split a connected component into its individual graph
edges; that is a separate atomization problem.