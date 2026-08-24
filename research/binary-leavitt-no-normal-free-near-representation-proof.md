---
rg: 2
id: binary-leavitt-no-normal-free-near-representation-proof
kind: route
title: Combine normal-state collapse with Leavitt factorization failure
target: binary-leavitt-has-no-normal-free-near-representation
requires:
  - normal-state-free-near-representation-forces-factorization
  - binary-leavitt-unit-group-fails-factorization-property
---

Assume a normal-state essentially free near representation of
`Q=L_(F_2)(1,2)^x` existed.  By
`normal-state-free-near-representation-forces-factorization`, it would imply
that `Q` has Kirchberg's factorization property.  This contradicts the
established claim `binary-leavitt-unit-group-fails-factorization-property`.
Therefore no such normal-state witness exists.
