---
rg: 2
id: clifford-twist-spectator-amplification-proof
kind: route
title: Amplify an exact actor model by an arbitrary spectator sign
target: kazhdan-and-transverse-packets-cannot-orient-clifford-twist
requires: []
---

Given `(pi,V_0)` satisfying `(KCT2)`, tensor every actor and packet matrix
with `I_(r+s)` and tensor `V_0` with `D_(r,s)`.  Since the spectator sign
commutes with every old matrix and squares to one, every multiplication,
conjugation, commutator, and covariance relation is unchanged.  Direct
calculation gives `(KCT4)` and `(KCT7)`.

For a Kazhdan actor the new sign lies in the exact commutant, so the
right-hand side of `(KCT5)` is zero.  For finitely many transverse packets,
their joint algebra still acts trivially on the spectator coordinate.  The
same family therefore simultaneously has zero defect and arbitrary mixed
orientation moment, proving the claim.
