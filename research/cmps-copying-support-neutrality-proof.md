---
rg: 2
id: cmps-copying-support-neutrality-proof
kind: route
title: Substitute the copied observables in every joint clause atom
target: cmps-copying-is-support-neutral
requires:
  - cmps-lemma20-is-radius-two-incidence-commutation
  - fano-cap-witness-sections-force-source-affine-safety
---

Lines 427--436 of Lemma 20 construct local variables `x_u` and seven copies
of every old clause.  In the perfect-completeness representation the proof
explicitly assigns the old observable to every local copy.  Functional
calculus therefore gives `A_(x_u)^b=A_x^b` for both spectral projections.
Multiplying the three commuting projections in a copied clause proves
`(CSN1)--(CSN3)` atom by atom, including equality of their ranks.

Affine unsafety is a property only of the set of nonzero atoms.  Equality of
supports transports the same odd xor certificate and proves `(CSN4)`.  The
source-support sandwich theorem then says that cap-valued witness ranges in
all later `R_*` occurrences would force the copied support to be affine-safe
inside its clause relation.  Contraposition proves the final firewall.

