---
rg: 2
id: universal-mf-quotient
kind: claim
title: The MF radical quotient is the universal MF quotient
distinct_from:
  literal-mf-radical-exact: This generic theorem constructs the universal quotient for every countable group; it does not compute the literal group's radical.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ManuscriptExactWrappers.lean
---

For every countable group `G`, let `Rad_MF(G)` be the intersection of the
kernels of all homomorphisms to unitary groups of positive
natural-dimension norm-matrix C-star coronas.  This radical is the kernel of
one such representation, the quotient `G/Rad_MF(G)` is MF, and every
homomorphism from `G` to a countable MF group factors through that quotient.
Consequently `G` is MF exactly when `Rad_MF(G)` is trivial.
