---
rg: 2
id: three-xor-violation-rank-proof
kind: route
title: Evaluate the affine diagonal pencil and its controlled Pauli lift
target: three-xor-violation-is-one-clifford-rank
requires:
  - clifford-commutator-rank-is-packet-dimension
---

The first diagonal entry of `M_b` is a permanent pivot and the second is the
violation bit, proving `(TXR1)`.  The two commutator relations therefore have
commutation matrix `M_b`.  Apply
`clifford-commutator-rank-is-packet-dimension` to obtain dimensions `2` and
`4`, and restrict to the first full-matrix factor to obtain multiplicities one
and two.  The controlled `I/Z` construction in the claim verifies existence
on every joint selector spectrum.  The artifact exhausts both right-hand
sides and all eight assignments.
