---
rg: 2
id: depthwise-canonical-kleene-proof
kind: route
title: Take the canonical microstate limit before compiled proof depth
target: depthwise-canonical-kleene-needs-no-uniform-runtime-gap
requires:
  - canonical-profile-kleene-higman
  - fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity
---

Fix a nonhalting index `e` and let `(U_k)` be any canonical-profile
microstate sequence for `Gamma_e`.  For fixed `N`, every relator in the
finite prefix `R_(e,N)` has defect tending to zero and every nonidentity word
in the finite trace window `F_(e,N)` has trace tending to zero.  Apply
`(DCK2)` and take `k->infinity`:

```text
 limsup_k ||w_e(U_k)-I||_2^2<=b_(e,N).
```

Now take `N->infinity`.  The marked word collapses in every canonical-profile
microstate sequence.  This verifies the NONHALT hypothesis of
`canonical-profile-kleene-higman`; `(DCK1)` is its HALT hypothesis.  Its
reverse-Kleene fixed point and effective Higman embedding therefore produce
a finitely presented nonhyperlinear group.

At no point is `C_(e,N)` compared with a defect at a depth depending on `k`.
For each fixed `N` it is merely one finite scalar multiplying a quantity that
tends to zero.  Hence arbitrary runtime growth of the constants is harmless.
