---
rg: 2
id: fixed-sample-pinch-sign-induction-proof
kind: route
title: Pinch and sign one reflection at a time for fixed sample size
target: slowly-growing-reflection-sample-rounds-to-commuting
requires:
  - joint-pinching-costs-linear-generator-gap
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
---

For fixed `t`, set `T_1=Q_1`.  Inductively pinch `Q_s` by the joint PVM of
the already commuting `T_1,...,T_(s-1)` and sign the resulting contraction.
The joint-pinching estimate bounds its movement by a constant depending only
on `s` times its commutators with the previous corrected reflections.
Triangle inequalities replace those commutators by raw pair commutators and
the earlier correction errors.  Since `s<=t` is fixed, induction gives a
modulus tending to zero.  The final diagonal choice of `t_n` is exactly the
one stated in the claim.
