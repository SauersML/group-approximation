---
rg: 2
id: universal-torsion-free-host-obstruction-proof
kind: route
title: Embed the Fournier-Facio group and push its nonsoficity and property (T) upward
target: universal-torsion-free-hosts-not-sofic-or-locally-indicable
requires:
  - fournier-facio-group-is-nonsofic
  - fournier-facio-torsion-free-skeleton
  - two-generator-fp-torsion-free-universal-whitehead-container
---

Let `G_FF` be the group fixed in [[fournier-facio-torsion-free-skeleton]]:
finitely presented, torsion-free, with property (T), and nonsofic by
[[fournier-facio-group-is-nonsofic]].  Let `Omega` contain a copy of every
finitely presented torsion-free group, so `G_FF <= Omega`.

1. A sofic approximation of `Omega` restricts to one of any subgroup, so
   soficity passes to subgroups.  `G_FF` is nonsofic, hence so is `Omega`.
2. `G_FF` is infinite and has property (T), so its abelianization is finite
   and it admits no epimorphism onto `Z`.  It is a nontrivial finitely
   generated subgroup of `Omega`, so `Omega` is not locally indicable.
3. Free groups are sofic.  Soficity is a condition on finite subsets, so
   directed unions of sofic groups are sofic.  An extension of a sofic group
   by an amenable group is sofic (Elek--Szabo, *On sofic groups*, J. Group
   Theory 9 (2006), arXiv:math/0305352, abstract: "the free product and
   amenable extensions of sofic groups are sofic as well"), and elementary
   amenable groups are amenable.  By induction over the construction of `C`,
   every group in `C` is sofic, and (1) gives `Omega not in C`.

For the master tester `E`,
[[two-generator-fp-torsion-free-universal-whitehead-container]] embeds every
countably generated recursively presented torsion-free group in `E`; finitely
presented torsion-free groups are among them, so `E` is such an `Omega`.  QED
