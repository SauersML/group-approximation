---
rg: 2
id: iwahori-low-gap-cluster-integralization
kind: claim
title: Low-gap Iwahori transport integralizes at connected-component scale
---

In the setup of `iwahori-fractional-transport-integralization`, let `E_n` be
the total mixed intertwining energy of the identity identification and choose
`a_n->0` with `E_n/a_n->0`.  Form the bipartite graph whose left vertices are
the source Iwahori isotypic blocks, whose right vertices are the target blocks,
and whose edges are the low-gap pairs

```text
lambda_(n,i,j) < a_n.
```

Then, after adding `o(d_n)` dimensions to each side carrying trivial Iwahori
representations, every connected component has equal stabilized source and
target dimension and there are componentwise unitaries

```text
W_(n,C): Q_(n,C) -> P_(n,C)
```

such that their direct sum `W_n` satisfies

```text
||W_n-I||_(2,d_n) -> 0,
sum_(s in S_B)||rho_n(s)W_n-W_n sigma_n(s)||_(2,d_n)^2 -> 0.
```

Here `I` is extended by zero on the added coordinates for the distance
comparison.  In particular the physical transport has been genuinely
integralized **between low-gap connected components**: no corrected unitary
moves mass between distinct components.

The statement deliberately stops at component scale.  A component may contain
many source and target irreducible types joined by chains of low-gap edges.
Splitting `W_(n,C)` further into orthogonal summands each supported on one
individual low-gap edge is the remaining atomization problem.