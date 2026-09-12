---
rg: 2
id: normal-toric-central-character-rfd-proof
kind: route
title: Split the phase-safe central clause character and approximate the resulting perfect product state
target: normal-phase-safe-toric-games-have-qa-one
requires:
  - toric-gap-is-a-relative-fd-central-word-face
---

Use `(RTF6)--(RTF10)`.  Normal closure first centralizes the Alice and Bob
components of every clause.  The phase-safe label is therefore a character
on a subgroup of the direct product of two abelian central-word groups.
Extend it to that direct product using divisibility of `T`, then restrict the
extension to the two factors.  State extension gives one-player states with
the prescribed unit-modulus word values, and their product GNS vector is
fixed by every determining binomial.  Approximate the two states separately
by finite-dimensional vector states using one-player RFD and tensor the
approximants.  This proves `omega_qa=1`.

