---
rg: 2
id: some-fp-infinite-torsion-group-has-bvc
kind: claim
title: "Some finitely presented infinite torsion group has BVC"
---

There is a finitely presented infinite torsion group `G` with BVC.

For a torsion group the virtually cyclic subgroups are exactly the finite
subgroups, since an infinite virtually cyclic group has an element of
infinite order.  So `G` has BVC iff its finite subgroups have bounded order
and fall into finitely many conjugacy classes of maximal finite subgroups.

- (=>) If finite `V_1, ..., V_n` witness BVC, every finite subgroup has order
  at most `max |V_i|`.  A maximal finite subgroup `M` lies in some
  `g V_i g^{-1}`, so `M = g V_i g^{-1}` by maximality.
- (<=) Bounded order makes every ascending chain of finite subgroups
  stabilize, so every finite subgroup lies in a maximal one.  Representatives
  of the finitely many classes of maximal finite subgroups witness BVC.

Any witness is in particular a finitely presented infinite torsion group,
which is Zaremsky Problem 1.11.

## Attempts

- **Deferred to Problem 1.11** (lanes z1-11-torsion-build and
  z1-11-torsion-block).  No finitely presented infinite torsion group is
  known at all, with or without BVC.  The small-cancellation torsion groups
  with few conjugacy classes are infinitely presented by construction.  They
  are direct limits of strictly increasing chains of normal subgroups
  `N_1 < N_2 < ...` of a finitely generated free group `F`.  Finitely many
  normal generators of `N = union N_i` would already lie in some `N_i`,
  forcing `N = N_i`.
