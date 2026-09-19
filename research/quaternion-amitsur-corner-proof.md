---
rg: 2
id: quaternion-amitsur-corner-proof
kind: route
title: Cut the negative quaternion sector into equal halves and apply Amitsur in one half
target: quaternion-packet-internalizes-unitary-amitsur-corner
requires:
  - one-sided-amitsur-oracle-has-two-unitary-corner-model
---

From `a^2=z` one has `a^*=a^(-1)=za`.  Since `Ez=-E`, this gives
`(iEa)^*=iEa`, and `(iEa)^2=E`; hence `(QAI2)` defines a projection.  The last
quaternion relation gives `bJb^(-1)=-J`.  Trace invariance under conjugation
therefore forces `tr(J)=0`, proving `(QAI3)` and `(QAI6)`.

The matrices in `(QAI5)` satisfy `a^2=b^2=-I`, while `bJb^(-1)=-J`; thus they
give the marked quaternion type and recover exactly the external half-corner
of the two-unitary construction.  This proves exact completeness.

In a finite evaluation, all compressed letters lie in the `r`-dimensional
corner `P M_D(C)P`, so the standard polynomial of degree `2r` vanishes there.
Finally `z-I=-2E` and `tr(P)=tr(E)/2`, yielding `(QAI7)--(QAI8)` exactly.
