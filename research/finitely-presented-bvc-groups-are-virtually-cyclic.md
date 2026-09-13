---
rg: 2
id: finitely-presented-bvc-groups-are-virtually-cyclic
kind: claim
title: Every finitely presented group with property BVC is virtually cyclic
distinct_from:
  groups-with-finite-evc-model-are-virtually-cyclic: that claim assumes a finite model for E_VC G, a strictly stronger hypothesis; this claim assumes only finite presentation plus BVC
---

The von Puttkamer–Wu conjecture (arXiv:1607.03790, Conjecture B): if `G` is finitely
presented and has finitely many virtually cyclic subgroups `V_1, ..., V_n` such that every
virtually cyclic subgroup of `G` is conjugate into some `V_i`, then `G` is virtually
cyclic. This is part (B) of `zaremsky-1-07-juan-pineda-leary-conjecture`.

## Attempts

- Necessary hypotheses. Without finite presentation it fails: Osin's torsion-free groups
  with two conjugacy classes have BVC (1607.03790, Remark (a)).
- Known classes: virtually solvable, one-relator, acylindrically hyperbolic, 3-manifold,
  CAT(0) with a rank-one isometry or `Z^2`, finitely generated linear, residually finite
  (see the root and the artifact).
- Tools already in the literature (1607.03790): BVC passes to finite-index subgroups (Lemma
  1.11); finite subgroups have bounded order (Lemma 1.7); `H_1(G;Z)` is finitely generated
  of rank at most one (Corollary 1.15); non-ascending HNN extensions have no BVC (Lemma
  2.4); `H ⋊_phi Z` has no BVC if `phi` has infinitely many twisted conjugacy classes
  (Lemma 1.19).
- Hardness. For torsion-free `G`, BVC holds exactly when finitely many elements have every
  element conjugate to a power of one of them (1607.03790, Corollary 1.5). So this
  conjecture forbids an infinite finitely presented torsion-free group with finitely many
  conjugacy classes. This lane found no reference deciding whether such a group exists.
- Lane z1-07-vc-proof (2026-09-13): working on elementary amenable groups of infinite
  Hirsch length, and on groups with positive first Betti number through Bieri–Strebel
  splittings plus Lemma 2.4.
