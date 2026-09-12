---
rg: 2
id: atlas-cross-jacobian-gauge-proof
kind: route
title: Evaluate every Jacobian block on the scalar orbit tangent
target: atlas-cross-jacobian-cannot-pay-the-gauge-mode
requires:
  - atlas-phase-jacobian-has-invertible-gauge-kernel
  - atlas-one-functional-gauge-pin-cannot-create-shrinkage
---

Scalar invariance says `F(exp(it)U)=F(U)`, and scalar equivariance says
`L(exp(it)U)=exp(it)L(U)`.  Differentiation at zero proves `(CJG1)`.
Substitution immediately kills every cross term and gives `(CJG3)`.

It remains only to justify the positivity assertion.  Write

```text
M=[[M_FF,M_FL],[M_LF,M_LL]]>=0.
```

If `M_LL=0`, then for arbitrary output vectors `x,y` and real `t`,
positivity of

```text
<(x,ty),M(x,ty)>
```

for both signs of `t` forces the linear coefficient
`2 Re <x,M_FL y>` to vanish.  Replacing `x` by `ix` also kills its imaginary
part, so `M_FL=0`; self-adjointness gives `M_LF=0`.  Hence no positive form
can retain a cross block while omitting the additive diagonal payment.

When `M_LL` is present, `(CJG3)` shows that its gauge payment depends only on
`L(U)`.  Thus using small nonlinear defect to bound that payment is precisely
the missing nonlinear-to-linear implication, not a consequence of the
cross-Jacobian construction.  This proves the firewall.
