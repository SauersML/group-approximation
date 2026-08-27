---
rg: 2
id: canonical-packet-trace-dilution-proof
kind: route
title: Tensor regular quotient models and count the two adjoint ranges
target: canonical-packet-traces-do-not-place-old-commutant-density
requires: []
---

Canonical trace convergence follows from the product trace formula and
eventual separation of each fixed old-group word by the residual chain.
Equation `(CPT2)` is the packet regular trace.

The packet adjoint action is trivial on `End(ell^2(Q_n))`, so its Reynolds
difference is

```text
I_(|Q_n|^2) tensor (R_A^B-R_B^B),
```

which proves `(CPT3)`.  The commutant of the left-regular `Q_n` action has
dimension `|Q_n|`; the packet tensor factor contributes all `|B|^2`
endomorphisms.  Dividing

```text
|Q_n| |B|^2
```

by `(|Q_n||B|)^2` proves `(CPT4)`.  Property `(T)` identifies the fixed
subgap spectral projection with the exact commutant in these exact
representations.

For `(CPT5)`, the adjoint representation of `Lambda` acts trivially on the
fixed factor `End(ell^2(B))`.  Hence every spectral projection of the old
adjoint Laplacian is the corresponding base spectral projection tensored
with the identity of rank `|B|^2`.  Both its rank and the ambient adjoint
dimension acquire this factor, so normalized spectral density is unchanged.
Apply canonical low-density vanishing to the base sequence.
