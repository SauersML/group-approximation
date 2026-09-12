---
rg: 2
id: clifford-same-phase-collision-countermodel-proof
kind: route
title: Realize every finite collision menu by Clifford half-space projections
target: clifford-same-phase-collisions-are-only-bimodule-returns
requires: []
---

For every `m>=2`, the complex Clifford algebra has a matrix representation by
self-adjoint involutions `A_1,...,A_m` with `(CSC1)`; one may take dimension
`2^floor(m/2)` and the usual iterated Pauli matrices.  Normalize the matrix
trace.  Conjugation by any `A_j`, `j!=i`, changes the sign of `A_i`, hence

```text
tau(A_i)=0.
```

Similarly conjugation by `A_i` changes the sign of `A_iA_j`, so
`tau(A_iA_j)=0`.  Expanding `P_i=(1+A_i)/2` gives `(CSC2)`.  Since `P_i,P_j`
are projections,

```text
||P_iP_j||_2^2
 =tau(P_jP_iP_j)
 =tau(P_iP_j)
 =1/4.                                                       (CSC6)
```

Moreover `A_iP_i=P_i` and `P_jA_j=P_j`, which proves `(CSC3)`.

For `i!=j`, anticommutation and involutivity give

```text
A_iA_jA_iA_j=-A_i^2A_j^2=-1.
```

Therefore `(CSC4)` holds for every `Y`, with no reducing or spectral
hypothesis.  If a vector belonged to both positive eigenspaces, then
`A_iA_jv=v` while anticommutation also gives `A_iA_jv=-A_jA_iv=-v`; hence the
vector is zero, proving `(CSC5)`.

Tensoring all matrices with an identity preserves every displayed identity.
Tensoring with an independent packet representation does as well, after
taking the packet carrier tensor the Clifford factor.  Thus the obstruction
cannot be removed by amplification, fixed packet exactification, or any
finite number of additional marked copies whose only analytic input is
spectral collision.
