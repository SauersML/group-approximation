---
rg: 2
id: binary-leavitt-purely-singular-near-representation-proof
kind: route
title: Specialize Kahl--Schneider and eliminate the normal state component
target: binary-leavitt-hyperlinear-iff-singular-near
requires:
  - hyperlinear-near-representation-criterion
  - binary-leavitt-unit-group-is-minimally-almost-periodic
  - map-free-near-state-is-purely-singular
---

If `Q` is hyperlinear, Kahl--Schneider Theorem 5.12(d), recorded in
`hyperlinear-near-representation-criterion`, produces a Hilbert space `H`, a
state `phi` on `B(H)` and a `phi`-near representation `pi` whose induced
character is the regular character.  Since
`binary-leavitt-unit-group-is-minimally-almost-periodic` and `Q` is nontrivial,
`map-free-near-state-is-purely-singular` implies that `phi` is purely
singular.  This gives condition 2.

Conversely, condition 2 is already condition (d) of Kahl--Schneider Theorem
5.12, with an additional restriction on the state, so it implies that `Q` is
hyperlinear.  Thus the two conditions are equivalent.
