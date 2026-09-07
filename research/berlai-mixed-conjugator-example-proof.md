---
rg: 2
id: berlai-mixed-conjugator-example-proof
kind: route
title: Substitute d=1 and V=a_2 into the one-sided theorem
target: berlai-mixed-conjugator-example-is-sofic
requires: [one-sided-conjugator-one-relator-groups-are-sofic]
artifacts:
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
---

In `F(a,b)`, `b^(-1)ab^2=b a_2`, where `a_2=b^(-2)ab^2`. Thus the
one-sided theorem applies with `d=1,V=a_2`. Its kernel relators are

    (a_(i+2)^(-1) a_(i+1) a_(i+2))^(-1)
      a_i^l
    (a_(i+2)^(-1) a_(i+1) a_(i+2)) = a_i^k.

The conjugator is conjugate to the next generator, so the triangular
cyclic-amalgam construction applies. This proves the claimed parameters,
including `l=1,k=2`.
