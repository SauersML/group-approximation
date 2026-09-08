---
rg: 2
id: kervaire-laudenbach-holds-for-mf
kind: claim
title: Nonsingular equations over countable MF groups have solutions in MF overgroups
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that assumes hyperlinear coefficients; this uses norm-corona MF coefficients directly and assumes no implication between the two approximation classes.
  kervaire-laudenbach-nonsingular-conjecture: that asks for every coefficient group; this proves the MF case and does not eliminate a kernel inside an arbitrary group's common approximation radical.
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
  - research/artifacts/nonsingular-equation-replay.json
---

Let `G` be a countable MF group in the norm-corona convention and let
`w in G*<t>` have nonzero `t`-exponent. The coefficient map
`G -> (G*<t>)/<<w>>` is injective, and the equation has a solution in a
countable MF group containing `G`.

More precisely, any fixed faithful embedding of `G` into a norm-corona
unitary group can be retained while adjoining a root inside that same
ambient unitary group. The countable image of the resulting solution map
is the asserted MF overgroup. The universal relative presentation itself
is not asserted to be MF.

Every countable MF group also embeds in a countable MF group that solves
every nonsingular one-variable equation with coefficients in itself, by
repeating the same construction on its successive countable stages.

This is a consequence of the classical matrix root theorem. No priority
claim or resolution of the universal conjecture is asserted.
