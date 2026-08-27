---
rg: 2
id: bcs-projection-atlas-equivalence-proof
kind: route
title: Diagonalize each context and identify its shared signed marginals
target: bcs-corner-model-is-a-compatible-projection-atlas
requires: []
---

Starting with `(BPA1)`, expand `(BPA2)`. Orthogonality gives
`V_(c,x)^*=V_(c,x)`, `V_(c,x)^2=q`, and contextwise commutation. For a sign
assignment `b`, multiplication of the spectral factors gives

```text
product_(x in U_c) (q+b_x V_(c,x))/2
 = p_(c,b) if b in R_c, and 0 otherwise.
```

Thus every forbidden BCS atom is zero, while `(BPA3)` makes the variable
images context independent. The universal property gives the unital corner
homomorphism.

Conversely, commuting self-adjoint involutions in one context have the joint
spectral projections displayed above. Forbidden atoms are zero by the BCS
relations, the allowed atoms are orthogonal and sum to `q`, and their signed
marginal is the image of the variable. Since that image is shared between
contexts, `(BPA3)` follows.
