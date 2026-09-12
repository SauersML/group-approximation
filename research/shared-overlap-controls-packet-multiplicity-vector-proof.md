---
rg: 2
id: shared-overlap-controls-packet-multiplicity-vector-proof
kind: route
title: Subtract the common subrepresentation and charge both complements
target: shared-overlap-controls-packet-multiplicity-vector
requires:
  - finite-group-shared-overlap-polar-alignment
---

Let `K_i` and `W:K_1->K_2` be given by `(OPA1)`. Their restricted
representations are equivalent, so they have one common multiplicity vector
`kappa`. Decompose

```text
mu_i=kappa+nu_i,
```

where `nu_i` is the multiplicity vector on `K_i^perp`. Coordinatewise
triangle inequality gives

```text
sum_sigma dim(sigma)|mu_1(sigma)-mu_2(sigma)|
 <= sum_sigma dim(sigma)(nu_1(sigma)+nu_2(sigma))
 = (m_1-dim K_1)+(m_2-dim K_2).
```

Now use `m_i<=(1+zeta)d` and
`dim K_i>=(1-4eta^2)d`. Each complement has dimension at most
`(zeta+4eta^2)d`, proving `(OMV1)`.
