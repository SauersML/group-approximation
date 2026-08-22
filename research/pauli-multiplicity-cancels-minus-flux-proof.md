---
rg: 2
id: pauli-multiplicity-cancels-minus-flux-proof
kind: route
title: Tensor the two oscillator transports with anticommuting Pauli matrices
target: p3-minus-flux-is-cancelled-by-pauli-multiplicity
requires: []
---

For every source operator `pi(g)`, covariance of `A` becomes

```text
(A tensor X)(pi(g) tensor I)(A* tensor X)
 =(A pi(g) A*) tensor I,
```

and similarly for `B tensor Z`.  Hence all covariance witnesses are
unchanged.  Meanwhile

```text
(A tensor X)(B tensor Z)=AB tensor XZ,
(B tensor Z)(A tensor X)=BA tensor ZX
                       =(-AB) tensor (-XZ)
                       =AB tensor XZ.
```

This proves exact commutation.  Normalized traces and normalized-HS norms
factor over the tensor product, so the cancellation has constant density
and zero defect in every amplification.
