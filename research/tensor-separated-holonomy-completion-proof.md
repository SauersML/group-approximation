---
rg: 2
id: tensor-separated-holonomy-completion-proof
kind: route
title: Tensor the losing multiplicity space with canonical holonomy microstates
target: tensor-separated-holonomy-controller-is-circular
requires: []
---

Let `sigma_n` be canonical-trace matrix microstates for `H`.  Replace every
base verifier block `B` by `B tensor 1_(d_n)` and assign

```text
u_l=F_l tensor sigma_n(h_l)
```

on the selected carrier.  For a controller relator `rho`, the fixed flag
product is the identity by hypothesis, so

```text
rho(u)-1=1 tensor (rho(sigma_n)-1).
```

The normalized Hilbert--Schmidt norm of the right side is unchanged by the
first tensor factor and tends to zero.  The selected projection becomes
`E tensor 1_(d_n)`, whose normalized trace is exactly `tau(E)`.  Likewise,
for each fixed controller word `v`,

```text
tr(v(u))=tr(F_v) tr(v(sigma_n)),
```

so every finite tensor-product canonical profile is matched.  This proves
the asserted completion and rules out `(TSH2)`.

