---
rg: 2
id: hnn-transports-forbidden-radical-atom-types-proof
kind: route
title: Restrict to the finite radical subgroup and apply HNN type alignment
target: hnn-transports-forbidden-radical-atom-types
requires:
  - boolean-violation-is-one-raw-radical-qubit-drop
  - finite-group-shared-overlap-polar-alignment
  - shared-overlap-controls-packet-multiplicity-vector
---

The selectors and `J` are central. The words `P_a` use only commuting row
generators and `Q_a` only commuting column generators, so both are
involutions commuting with the selectors. Their mutual commutator is a word in
the finite selector center. Thus `(HRA1)` is a finite class-two group.

At selector character `a`, `(BRD3)` says the exponent vectors of `P_a,Q_a`
are the left and right kernels of the commutation matrix. Hence both commute
with every packet generator on that sector. Their signs are precisely the two
radical characters, proving the four-type assertion.

Britton normal form embeds the base after adjoining the stable letter. In an
exact representation, that letter is a unitary intertwiner between the two
restrictions, so every irreducible multiplicity agrees. For an approximate
tuple, exactify the two fixed `E_a` tables and average/polar-align the evaluated
stable letter. The shared-overlap multiplicity theorem bounds the unmatched
weighted type mass by `C sqrt(E)`. All tables are fixed, so `C` is independent
of ambient dimension.
