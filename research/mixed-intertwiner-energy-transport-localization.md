---
rg: 2
id: mixed-intertwiner-energy-transport-localization
kind: claim
title: Mixed intertwiner energy localizes physical mass as a transportation cost
---

Let `H` be a group, let `S` be a finite subset, and let

```text
rho,sigma : H -> U(d)
```

be exact finite-dimensional unitary representations.  Let `(P_i)` and
`(Q_j)` be finite orthogonal decompositions of the identity by projections
which reduce `rho` and `sigma`, respectively.  For a unitary `U in U(d)` put

```text
m_(i,j) = ||P_i U Q_j||_2^2,
E(U) = sum_(s in S) ||rho(s)U-U sigma(s)||_2^2.
```

For each pair define the bottom mixed-intertwiner energy

```text
lambda_(i,j)
 = inf_{0 != T in P_i M_d Q_j}
     (sum_(s in S) ||rho(s)T-T sigma(s)||_2^2) / ||T||_2^2,
```

with `lambda_(i,j)=+infinity` when the block is zero.  Then:

1. `m` is an exact transportation plan with marginals

```text
sum_j m_(i,j)=tr_d(P_i),
sum_i m_(i,j)=tr_d(Q_j);
```

2. its spectral transportation cost is bounded by the actual intertwining
   defect:

```text
sum_(i,j) lambda_(i,j) m_(i,j) <= E(U);
```

3. consequently, for every `a>0`,

```text
sum_(lambda_(i,j) >= a) m_(i,j) <= E(U)/a.
```

Thus if `E(U)->0` and `a->0` slowly enough that `E(U)/a->0`, all but `o(1)`
of the **physical normalized trace mass** is transported through block pairs
whose mixed spectral bottom tends to zero.  This is stronger than saying
that a low-energy subspace has `o(d^2)` Hilbert-space dimension: it locates
the mass of the actual almost intertwiner among representation blocks.
