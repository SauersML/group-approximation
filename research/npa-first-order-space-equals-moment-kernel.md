---
rg: 2
id: npa-first-order-space-equals-moment-kernel
kind: claim
title: The critical-face first-order space has the same dimension as the compressed moment kernel
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

For every `k >= 2`,

```text
dim V_k = dim ker Phi_k,
```

where `ker Phi_k = { y : N_k^T Gamma_k(y) N_k = 0 }` carries no pin, and `V_k`
is cut out by `Phi_k(y) = lambda u_k u_k^T` together with `y_[identity] = 0`.

The two corrections cancel exactly.  A level-independent witness `y*` with
`Phi_k(y*) = u_k u_k^T` makes the `lambda`-line a genuine extra dimension, so
the solution set of `Phi_k(y) = lambda u_k u_k^T` is `ker Phi_k + R y*` and the
free `lambda` adds one.  In the other direction the critical-face vectors
`y_0(delta)` satisfy `Gamma_k(y_0) N_k = 0`, hence lie in `ker Phi_k`, and have
identity coordinate `1`; so the identity-coordinate functional is not identically
zero on `ker Phi_k` and the pin `y_[identity] = 0` removes exactly one dimension.

This is a statement about dimensions only.  It converts the dimension law
`dim V_k = 2k+3` into the nullity statement `dim ker Phi_k = 2k+3`, which is
what the shell arguments actually address, and it is the step of that program
that is unconditionally in hand.
