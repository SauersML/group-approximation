---
rg: 2
id: pure-finite-group-operator-scaling-collapses-to-multiplicity-proof
kind: route
title: Combine the uniform finite-group gap with the exact shrinkage formula
target: pure-finite-group-operator-scaling-collapses-to-multiplicity
requires:
  - finite-group-intertwiner-laplacian-gap
  - finite-group-intertwiner-shrinkage-formula
---

Let `kappa=kappa(H,S)>0` be supplied by
`finite-group-intertwiner-laplacian-gap`.  Since `a_n->0`, eventually
`a_n<kappa`, and hence

```text
K_(a_n)=Hom_H(sigma_n,rho_n).
```

This is `(PFG1)`.

The two representation spaces have the same dimension `d_n`, so apply
`finite-group-intertwiner-shrinkage-formula` to that exact intertwiner space.
It gives

```text
max_X (dim X-dim K_(a_n)(X))
 = (1/2) sum_lambda d_lambda
   |m_(n,lambda)-n_(n,lambda)|.
```

Divide by `d_n` to obtain `(PFG2)`.  The equivalence between linear shrinkage
and a positive normalized weighted `L1` multiplicity mismatch is immediate.
No asymptotic compactness or operator-scaling theorem is needed.
