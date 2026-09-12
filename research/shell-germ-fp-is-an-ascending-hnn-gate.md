---
rg: 2
id: shell-germ-fp-is-an-ascending-hnn-gate
kind: claim
title: Finite presentation of the shell germ group is equivalent to an ascending HNN condition on its single-ray near group
artifacts:
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

For an infinite finitely generated input P and enumeration nu, use
R=R_nu, eta, s, and Q from the shell fiber-product claim. Then Q is
finitely presented exactly when R is finitely presented and there are
a finitely generated subgroup B<=ker(eta) and epsilon in {1,-1} with

    B <= s^epsilon*B*s^-epsilon,
    ker(eta)=union_(n>=0) s^(epsilon*n)*B*s^(-epsilon*n).

Equality in the first inclusion is allowed. This condition is necessary
for A_1 to be finitely presented; its sufficiency for A_1 is open.
