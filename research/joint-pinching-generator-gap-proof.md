---
rg: 2
id: joint-pinching-generator-gap-proof
kind: route
title: Diagonalize the commuting adjoint involutions and count Fourier weight
target: joint-pinching-costs-linear-generator-gap
requires: []
---

The maps `Ad(S_i)` are commuting selfadjoint involutions of the Hilbert space
`L_2(M,tau)`.  Their simultaneous spectral projections are

```text
Pi_a=2^(-k) sum_(b in F_2^k) (-1)^(a dot b) Ad(S_1)^(b_1)...Ad(S_k)^(b_k).
```

Set `R_a=Pi_a(R)`.  Orthogonality gives `(JPG3)`.  The zero-character
projection is exactly the conditional expectation onto the common
commutant, equivalently the pinching by the joint spectral PVM.  On the
`a`-summand, `[R_a,S_i]` is zero when `a_i=0` and has norm `2||R_a||_2`
when `a_i=1`.  Summing proves `(JPG4)`, hence `(JPG2)`.  Choosing a nonzero
operator in a weight-one or weight-`k` spectral subspace proves sharpness
whenever that subspace is present; the standard tensor-Pauli models realize
both endpoints for every `k`.

