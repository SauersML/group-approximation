---
rg: 2
id: code-gap-finite-p-semigroup-interpolation-proof
kind: route
title: Interpolate code-noise L2 decay with Markov endpoint contractivity
target: code-gap-gives-finite-p-inverse-square-root
requires:
  - code-laplacian-has-uniform-cp-green-approximants
---

Put `T_t=P_t-E`.  It has `L_2` norm at most `exp(-delta t)` by `(CGP1)`
and `L_infinity` norm at most two because both `P_t` and `E` are unital
positive contractions.  Complex interpolation gives

```text
 ||T_t||_(p->p)
   <= 2^(1-2/p) exp(-2delta t/p).                        (CGP3)
```

For `EX=0`, `P_tX=T_tX`; the semigroup formula and `(CGP3)` give

```text
 Delta^(-1/2)X
   =pi^(-1/2) integral_0^infinity t^(-1/2)P_tX dt,
```

and integration yields `(CGP2)`.  Tensoring the semigroup and expectation
with an identity matrix preserves `(CGP1)` and both endpoint norms, proving
the amplification statement.

For code characters, the kernel
`exp(-t wt(chi+psi)/L)` is positive definite, so its Schur multiplier is
Markov.  The code-distance bound places every non-fixed block above
`delta`, which verifies `(CGP1)` by block orthogonality.
