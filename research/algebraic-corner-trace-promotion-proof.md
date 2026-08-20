---
rg: 2
id: algebraic-corner-trace-promotion-proof
kind: route
title: Pull back the faithful canonical corner trace and restrict a Connes embedding
target: nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
requires: []
---

Represent `C[Gamma]` by the left regular representation. Faithfulness gives
`tau_Gamma(q)>0` for every nonzero projection `q`. If `Gamma` is hyperlinear,
there is a trace-preserving embedding of `L(Gamma)` into a tracial
ultraproduct of matrices (equivalently into `R^omega`). Compression by the
image of `q` gives such an embedding of the normalized corner.

The pullback `sigma=tau_q after Phi` is positive, unital, and tracial. Its
GNS null ideal is the pullback of the `tau_q`-null ideal of `Phi(B)`. Since
`tau_q` is faithful on the ambient finite von Neumann algebra, the GNS
completion identifies with `W^*(Phi(B)) subset qL(Gamma)q`. Restricting the
corner embedding to this von Neumann subalgebra proves that `sigma` is
Connes embeddable, contradicting the hypothesis on `B`.
