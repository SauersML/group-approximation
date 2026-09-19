---
rg: 2
id: fixed-pauli-pair-hs-rounding-proof
kind: route
title: Apply flexible Hilbert--Schmidt stability to the fixed D8 multiplication table
target: fixed-pauli-pair-hs-rounding
requires:
  - finite-schur-clifford-packet-flexible-hs-exactification
---

Functional calculus first replaces the two approximate self-adjoint
involutions by exact involutions at `O(epsilon)` cost.  The transferred
anticommutator defect is still `O(epsilon)`.  Together with the scalar
involution `J=-I`, this is an approximate representation of the fixed group

```text
D_8=<p,q,J | p^2=q^2=J^2=1, J central, [p,q]=J>.
```

Flexible finite-group Hilbert--Schmidt stability, specialized to this one
fixed multiplication table, gives an exact representation with universal
loss and flexible-dimension cost.  On its negative `J` sector the exact table
is precisely an anticommuting Pauli pair.

