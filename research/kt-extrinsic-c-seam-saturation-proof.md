---
rg: 2
id: kt-extrinsic-c-seam-saturation-proof
kind: route
title: Realize the approximate commutant and holonomy type by countable saturation
target: kt-extrinsic-c-seam-has-a-finite-satisfiability-criterion
requires:
  - kt-c-normalization-seam-is-a-relative-commutant-cocycle
  - kt-internal-c-seam-has-a-kazhdan-gap
  - kt-two-compressor-normalizer-cocycle-splits
---

Necessity follows by taking `z_n=z`.  Conversely, `(KES2)` says that every
finite part of the following countable continuous type is approximately
satisfiable in `R^omega`:

```text
z^*z=zz^*=1,
[z,x_j]=0                                      (j>=1),
z v_gamma-rho_gamma z=0                        (gamma in T),
r(u_A,z u_C)-1=0                               (r in Rel_S).  (KET1)
```

Tracial ultrapowers are countably saturated, so `(KET1)` has a realization.
Commutation with the dense set `X` gives `z in R' cap R^omega`.  The generator
intertwining equations propagate to every element of `Gamma`, and the finite
relator equations make `A |-> u_A`, `C |-> z u_C` a representation of `S`.
This proves `(KES1)`.  The warning about scope is essential: these equations
kill the finite C-normalization seam and preserve the external actor table,
but no assertion is made that they normally generate the entire kernel of
`P_A->G`.
