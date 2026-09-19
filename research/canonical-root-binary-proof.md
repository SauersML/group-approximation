---
rg: 2
id: canonical-root-binary-proof
kind: route
title: Apply canonical character convergence to the root word
target: canonical-root-coordinate-is-binary-not-an-l2-authenticator
requires: []
---

Canonical-delta convergence gives
`tr(g(U_n))->tau_Gamma(g)=1_(g=1)`.  Since `g(U_n)` is unitary,

```text
||g(U_n)-1||_2^2=2-2 Re tr(g(U_n)).
```

This proves the zero-or-two dichotomy.  If `g!=1`, every a priori bound
`limsup ||A_n||_2^2<=B` yields the vacuous estimate with coefficient `B/2`.
If `g=1`, the root defect tends to zero, so
`||A_n||_2^2<=K||g(U_n)-1||_2^2+o(1)` is equivalent to `||A_n||_2->0`.
Applying this to the bounded OHR row proves the claim and isolates kernel
reflection as the missing implication.
