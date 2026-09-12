---
rg: 2
id: selector-free-spin-reset-independence-proof
kind: route
title: Compute the selector-reset restriction equation and realize every sign pair
target: selector-free-spin-reset-leaves-contexts-independent
requires:
  - fanizza-radical-charts-admit-common-symplectic-reset-subgroups
---

The common reset subgroup has one marked simple type `sigma`.  Each of the two
old chart simples restricts once to `sigma`, and a fresh Boolean selector has
two one-dimensional characters, so each fresh extension also restricts once
to `sigma`.  This gives `(SFI2)` and hence `(SFI3)`.

For existence, fix signs `a,b`.  Since `rho_a|_E` and `eta_b|_E` are both
unitarily equivalent to `sigma`, conjugate one model so that the restrictions
agree literally.  The defining universal property of `G_0 *_E G_1` now
extends these two representations to one representation of the amalgam.
Nothing in its relators compares `a` with `b`, so all four choices are exact.
Direct sums and conjugation by arbitrary unitaries in the multiplicity
commutant give the amplified statement.

The artifact prints the restriction matrices and exhausts the `2^(2k)` exact
character pairs for one through four selector bits.
