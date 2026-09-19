---
rg: 2
id: canonical-trace-literal-pi-return-proof
kind: route
title: Compute the packet Gram matrix and every outside-word overlap
target: canonical-trace-forbids-literal-pi-return
requires: []
---

Index the elements of `K` as `k_1,...,k_m`.  Relator defect and the fixed
word window give

```text
<k_i(U_n),k_j(U_n)> -> tau_Gamma(k_i^(-1)k_j)=delta_(ij).
```

Thus the Gram matrix tends to `I_m`, and the norm of orthogonal projection
onto their span is asymptotically computed by the Euclidean norm of the
overlap vector.  For `y notin K`, every coordinate satisfies

```text
<k_i(U_n),y(U_n)> -> tau_Gamma(k_i^(-1)y)=0.
```

Since `||y(U_n)||_2=1`, Pythagoras gives distance tending to one.  If
`y in K`, relator defect makes it `o(1)` from its named packet word, giving
distance zero.

For the phase compression, expand `P_zeta` by `(CTL3)`.  Every compressed
matrix coefficient is a sum of moments of `J^c k_i^(-1)y`.  Such a moment
can be nonzero under the canonical group trace only if that group element is
the identity, equivalently `y=k_i J^(-c) in K`.
