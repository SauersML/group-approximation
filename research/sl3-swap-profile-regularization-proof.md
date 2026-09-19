---
rg: 2
id: sl3-swap-profile-regularization-proof
kind: route
title: Tensor with a finite-quotient regular actor and an external balanced bit
target: congruence-tensor-regularizes-sl3-swap-profile
requires: []
---

Choose a residual chain of finite quotients `q_n:A->Q_n` separating larger
and larger finite subsets of `A`.  The representation

```text
a |-> lambda_(Q_n)(q_n(a)) tensor I_2,
s |-> I tensor diag(1,-1)
```

is exact because the external bit commutes with all of `A`.  Its actor trace
is eventually zero on each fixed nonidentity element, its swap trace is
zero, and its fold is the identity.  Tensoring it with an arbitrary
approximate assignment preserves normalized Hilbert--Schmidt relator
defects and multiplies each fold moment by one.
