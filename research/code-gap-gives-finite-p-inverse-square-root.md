---
rg: 2
id: code-gap-gives-finite-p-inverse-square-root
kind: claim
title: A code gap gives dimension-free finite-p inverse-square-root bounds
distinct_from:
  code-laplacian-has-uniform-cp-green-approximants: that constructs fixed-degree completely positive approximants with an L2 tail; this bounds the exact inverse square root on every finite Lp, but not at the endpoint.
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that still needs the coordinate Riesz/divergence assembly and an endpoint row or BMO estimate; this controls only its scalar inverse-square-root factor.
  junge-riesz-bmo-does-not-close-code-newton: that audits why the published endpoint tools do not close Newton; this records the positive finite-p consequence of the spectral gap.
---

Let `P_t=exp(-t Delta)` be a trace-preserving self-adjoint Markov semigroup
on a finite tracial von Neumann algebra, let `E` be its fixed-point
expectation, and suppose

```text
 ||(P_t-E)X||_2 <= exp(-delta t)||X||_2.                 (CGP1)
```

Then for every `2<=p<infinity`, on `ker E`,

```text
 ||Delta^(-1/2)X||_p
    <= 2^(1-2/p)sqrt(p/(2delta)) ||X||_p
    <= sqrt(2p/delta)||X||_p.                            (CGP2)
```

The same estimate holds at every matrix amplification, with the same
constant.

For the normalized Hamming generator on an exact code-character
decomposition,

```text
 Delta_(chi,psi)=wt(chi+psi)/L,
```

a relative code distance `delta` gives `(CGP1)`.  Thus the extra
`Delta^(-1/2)` factor in the code-coordinate inverse has a
dimension-independent completely bounded `L_p` norm of order
`sqrt(p/delta)` for every finite `p`.

This is genuinely weaker than `(CRM3)`: the bound grows with `p` and gives
no `L_infinity` or physical common-cut estimate.  It can be composed with a
finite-`p` tangent-module Riesz/divergence estimate only after the code
two-form row has been placed in the correct row/column module.  That module
identification, and the promotion from finite moments to one approximately
reducing physical projection, remain open.
