---
rg: 2
id: one-gram-vector-decodes-a-finite-bcs-strategy-proof
kind: route
title: Vectorize the common Gram operator and read every BCS loss exactly
target: one-gram-vector-decodes-a-finite-bcs-strategy
requires: []
---

Normalize `psi_G=vec(G)/||G||_2`.  Alice measures the context PVM and Bob
measures the conjugate binary PVM of the involution `B_x`.  Vectorization and
cyclicity of normalized trace give exactly

```text
Pr[a_x!=b | c,x]
  =||A_(c,x)G-GB_x||_2^2/(4||G||_2^2),

Pr[Alice returns a forbidden answer | c]
  =||F_cG||_2^2/||G||_2^2.
```

The losing event is contained in the union of these two events.  Averaging
with the rational question distribution proves `(OGV4)`.  Applying the fixed
finite-dimensional game-value ceiling `theta<1` to this genuine tensor-product
strategy gives `(OGV5)`.  This is the complete proof recorded in
`one-gram-vector-decodes-a-finite-bcs-strategy`.
