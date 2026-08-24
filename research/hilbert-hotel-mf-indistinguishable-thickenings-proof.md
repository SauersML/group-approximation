---
rg: 2
id: hilbert-hotel-mf-indistinguishable-thickenings-proof
kind: route
title: Factor every target map uniquely through the extension quotient
target: hilbert-hotel-mf-indistinguishable-thickenings
requires:
  - full-mf-radical-absorber
  - full-mf-radical-dynamical-rigidity
  - hilbert-hotel-block-cover-is-unconditional
artifacts:
  - research/hilbert-hotel-mf-indistinguishable-thickenings.md
---

Every homomorphism `f:E->M` to an MF group kills the image of `A`, hence its
normal closure `N`.  It therefore factors uniquely through `pi`.  Conversely
every homomorphism from `B` pulls back along `pi`, proving `(T1)` naturally in
`M`.

Compact targets are separated by their finite-dimensional unitary
representations, and countable complex linear targets are MF.  Finite groups
are MF.  Applying `(T1)` in these subcategories yields the Bohr, linear, and
profinite conclusions.  Applying it to all MF targets gives the isomorphism
of universal MF-visible quotients.

For the direct product, the kernel is the first factor.  Finite presentation
of a direct product follows by taking the two finite presentations and adding
finitely many cross-commutation relations.  Nonisomorphism from the base can
be arranged, for example, by choosing a base with a different universal
MF-visible quotient; the projection already has nontrivial kernel in every
case.

