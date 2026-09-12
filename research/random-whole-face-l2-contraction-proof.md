---
rg: 2
id: random-whole-face-l2-contraction-proof
kind: route
title: Use the Pythagorean identity for a random face projection
target: random-whole-face-pinchings-contract-transverse-l2
requires:
  - repeated-ldpc-adjoint-face-hamiltonian-gap
---

Put `Y=X-E_KX`.  Since `K` lies in every `ran(Phi_c)`,
`Phi_cE_K=E_KPhi_c=E_K`; in particular `Phi_cY` remains orthogonal to `K`.
As `Phi_c` is an orthogonal projection,

```text
||Phi_cY||_2^2=||Y||_2^2-||(I-Phi_c)Y||_2^2.
```

Averaging and applying `(RWF1)` proves `(RWF2)`.  Conditional expectation
at each independent step gives `(RWF3)` by induction.  Tensoring every
`Phi_c` with a matrix identity preserves orthogonal projection and the same
gap, proving complete amplification.
