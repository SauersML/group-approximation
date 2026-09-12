---
rg: 2
id: leavitt-two-compressor-core-has-modular-normal-form
kind: claim
title: The elementary two-compressor core is a locally finite lamp group by the modular group
artifacts:
  - research/leavitt-two-compressor-modular-normal-form-proof.md
distinct_from:
  leavitt-two-compressor-diagonal-kernel-is-locally-finite: that only places the diagonal normal closure in an ultramatricial block group and leaves the quotient unidentified; this computes both the full lamp kernel and the quotient normal form.
  leavitt-two-compressor-covariance-triangle-has-marked-models: that models a weaker abstract covariance table with only the order-three relative word; this identifies the additional order-two kernel word of the literal subgroup.
---

Let `H=GL_5(F_2)` and let `X={0,1}^N`.  The downstairs elementary
two-compressor core has the exact normal form

```text
B_EL ~= C_lc(X,H) semidirect (C_2*C_3).               (MNF1)
```

The locally constant lamp group is the normal closure of the original
diagonal subgroup.  If `t=tau_0` and `r=tau_1 tau_0^(-1)`, then

```text
r^3=1,                    (r t^(-1))^2=1,             (MNF2)
```

and these are the complete relations among the two prefix generators:
`s=r t^(-1)` and `r` generate `C_2*C_3`.

In particular the literal two-compressor kernel contains the fixed word
`(tau_1 tau_0^(-2))^2`, which is nontrivial in the weaker presentation
`<t,r | r^3=1>`.  The result does not decide whether the semidirect product
is operator-MF with a visible lamp: generic permanence from a locally finite
normal kernel and a sofic quotient is not invoked.

DERIVATION
leavitt-two-compressor-modular-normal-form-proof
