---
rg: 2
id: gauge-pair-common-source-proof
kind: route
title: Mix paired gauge atoms and compute the common source Gram exactly
target: gauge-pair-holonomy-needs-one-source-moment
requires: []
---

In a selected packet corner, pair coordinate atoms `(a,b)` and `(-a,-b)`.
They have the same logical product.  Put a Hadamard on each pair and attach
independent free phases to coordinate atoms, obtaining a finite-support
corner unitary `V` which commutes with the logical product but not with the
individual shares.

For any analytic projection `Q` inside that corner define `S_c=V_c^*Q`.
Unitarity gives the exact identity `S_c^*S_c=Q`, independent of context.
For a target share `a_(c,u)` and original shared word `Z_u`, the complete row
is

```text
mu_(c,u)=||a_(c,u)V_c^*Q-V_c^*QZ_u||_2^2.
```

This is a fixed finite linear combination of mixed trace moments.  Summing
one share and the product per gauge pair controls the other share by
telescoping.  Target predicate residuals vanish on the selected packet, so
the sum of these `mu` is the sole remaining analytic row.  For `Q` equal to
the full corner it reduces to one overlap scalar
`2tau(Q)-2Re tau(VaV^*ZQ)`.  Countable amplification and gauge-orbit
covariantization realize all pair Hadamards exactly, while a vanishing HALT
source makes the row vacuous.  Thus common-source alignment is proved and
only the mixed moment remains.
