---
rg: 2
id: stw63-zstable-hull-central-bridge-proof
kind: route
title: Place a central Jiang--Su copy in the hull sequence algebra
target: stw63-zstable-hull-gives-pairwise-uniqueness
requires:
  - joint-central-z-bridge-forces-approximate-uniqueness
---

Central-sequence absorption for the unital `Z`-stable algebra `C` gives a
unital homomorphism

```text
rho:Z -> C_infinity intersect C'.
```

The inclusion `C subset B` induces `C_infinity -> B_infinity`.  Its image
commutes with both `phi(Z)` and `psi(Z)`, since both ranges lie in `C`.
Thus `rho` is a joint central-sequence bridge for the chosen pair in
`B_infinity`.  The joint-bridge theorem produces implementing unitaries in
`B`.
