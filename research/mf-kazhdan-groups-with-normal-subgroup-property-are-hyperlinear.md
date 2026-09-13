---
rg: 2
id: mf-kazhdan-groups-with-normal-subgroup-property-are-hyperlinear
kind: claim
title: MF Kazhdan groups whose normal subgroups are finite or of finite index are hyperlinear
distinct_from:
  kazhdan-mf-hyperlinear-fragment: that gives a nontrivial hyperlinear quotient of any Kazhdan MF group and hyperlinearity for simple ones; this upgrades hyperlinearity from simple sources to every Kazhdan MF source with the normal subgroup property, by running that fragment on a finite-index normal subgroup and inducing back.
  mf-hyperlinear-of-finite-normal-quotient: that converts a finite normal kernel with hyperlinear quotient into hyperlinearity; this one handles the case where the hyperlinear residual has finite index, which that converter never sees.
  mf-implies-hyperlinear: that asks for every MF group; this settles only MF groups with property (T) and the normal subgroup property.
---

**Statement.** Let `G` be a countable group that is MF in the weak
norm-matrix-corona convention of `mf-implies-hyperlinear`. Suppose every
normal subgroup of `G` is finite or has finite index.

1. If every nontrivial finite-index normal subgroup of `G` has a nontrivial
   hyperlinear quotient, then `G` is hyperlinear.
2. In particular, if `G` has property (T), then `G` is hyperlinear.

Part 2 covers every Kazhdan MF group with the normal subgroup property: just
infinite Kazhdan MF groups, and MF finite central extensions of simple
Kazhdan groups (normal subgroups either lie in the finite center or have
finite index).

**Scope.** This is a structural fragment of `mf-implies-hyperlinear`, not a
new class of examples. The known Kazhdan groups with the normal subgroup
property, such as higher-rank irreducible lattices with Margulis' theorem,
are linear and already hyperlinear. The new content is for a hypothetical
non-linear Kazhdan group with the normal subgroup property that is MF. By
`mf-refutation-yields-nonhyperlinear-group`, any counterexample to the root
must avoid this class, so an MF non-hyperlinear group must have a normal
subgroup that is infinite and of infinite index, or must fail property (T)
in the sense of part 1.

No novelty search was run outside the repository. The Bachner--Dogon--Lubotzky
source arXiv:2508.17392v3 contains no statement about the normal subgroup
property or just infinite groups (source text grepped on MSI).
