---
rg: 2
id: kt-wreath-from-relative-actor-exactification
kind: route
title: Kill the Kun--Thom wreath from actor-only canonical exactification
target: non-hyperlinear-group
requires:
  - kt-wreath-relative-canonical-actor-exactification
  - kun-thom-nonsofic-wreath
  - commutant-no-growth
---

Assume a canonical microstate sequence for the explicit wreath and apply
`kt-wreath-relative-canonical-actor-exactification`.  Pad the base-lamp
involution by the identity on the `o(d_n)` new dimensions.  The fixed Kazhdan
set of `Gamma` and the conjugation representation on Hilbert--Schmidt
operators project it to `pi_n(Gamma)'` with `o_2(1)` error; spectral rounding
inside that finite-dimensional algebra makes it an involution.

Conjugate by `pi_n(t)`.  It lies in
`pi_n(t Gamma t^(-1))'`, which equals `pi_n(Gamma)'` by
`commutant-no-growth`.  Hence every fixed `gamma in
Gamma\t Gamma t^(-1)` asymptotically fixes the transported lamp.  Translating
back to the original microstate contradicts the canonical separation of the
two coordinate involutions indexed by `tGamma` and `gamma tGamma`.  Therefore
the microstate sequence cannot exist and the explicit Kun--Thom wreath is
non-hyperlinear.
