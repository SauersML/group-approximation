---
rg: 2
id: full-core-central-relative-tangent-vanishing-proof
kind: route
title: Flip a full-core-central tangent through the first cubic
target: full-core-central-relative-tangent-is-zero-near-first-cubic
requires: []
---

Let `A=XS^2` and `U=A^3`.  From `[h,S]=0` and `XhX=-h` one obtains
`Ad_A(h)=-h`, hence also `Ad_U(h)=-h`.  For either the Hilbert--Schmidt or
operator norm,

```text
2||h||_p=||UhU^*-h||_p
 <=||(U-1)hU^*||_p+||h(U^*-1)||_p
 <=2||U-1||_op ||h||_p.
```

When `||U-1||_op<1`, this forces `h=0`.  The fixed-core tangent equations
themselves impose only `XhX=-h` and `[h,R]=0`; adding `[h,S]=0` is exactly the
extra full-core-central ansatz shown here to annihilate the tangent.  No
claim about a single unsigned spectral cut is used.
