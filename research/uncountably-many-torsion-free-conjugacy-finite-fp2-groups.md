---
rg: 2
id: uncountably-many-torsion-free-conjugacy-finite-fp2-groups
kind: claim
title: "There are uncountably many pairwise non-isomorphic torsion-free groups of type FP_2 with finitely many conjugacy classes"
distinct_from:
  torsion-free-fp-groups-embed-in-fp2-conjugacy-finite-groups: that is an embedding theorem for every torsion-free input of type FP; this asks only for an uncountable family, which that theorem gives through Leary's groups.
  uncountably-many-fp2-groups-have-faithful-ha2-actions: that asks for uncountably many FP_2 groups with faithful [HA_2] actions; this is the conjugacy-finite special case, which gives that through the two-sided translation Γ × Γ ↷ Γ.
  some-infinite-fp-torsion-free-group-has-finitely-many-classes: that asks for one finitely presented example; there are only countably many finitely presented groups, so this family is necessarily almost entirely not finitely presented.
---

**OPEN.** There is a family `(Γ_i)` of torsion-free groups of type FP_2, each with
finitely many conjugacy classes, realizing uncountably many isomorphism types.

Routes in: `uncountably-many-conjugacy-finite-fp2-groups-via-embedding`.
Route out: `uncountably-many-ha2-actors-via-conjugacy-finite-fp2-groups`, into the
first part of Problem 1.20.

**Equivalent single-group form (pigeonhole, no new input).** By
`fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup` each `Γ_i = P_i/N_i` with
`P_i` finitely presented and `N_i` perfect. There are countably many finitely
presented groups, so the claim holds iff some one finitely presented `P` has
uncountably many perfect normal subgroups `N` with `P/N` torsion-free and
conjugacy-finite. Distinct types are then automatic: a given `Q` occurs as `P/N`
for at most countably many `N`, each the kernel of a surjection `P → Q`, and there
are countably many homomorphisms from the finitely generated `P` to the countable
`Q`.

**Not known even for one group.** No infinite group of type FP_2 with finitely
many conjugacy classes is recorded in the graph; the known Osin groups are
finitely generated only.
