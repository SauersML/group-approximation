---
rg: 2
id: fa-groups-finitely-many-homs-to-rel-hyperbolic-groups
kind: claim
title: A finitely generated group with property FA has only finitely many non-parabolic homomorphisms to a relatively hyperbolic group up to conjugacy, and a one-ended hyperbolic group without virtually cyclic splittings has finite Out
distinct_from:
  property-t-implies-property-fa: that is Watatani's theorem giving FA from property (T); this is the Drutu--Sapir finiteness of homomorphisms from FA groups into relatively hyperbolic groups, which consumes FA.
  hyperbolic-nonelementary-centralizer-finite: that bounds centralizers of non-elementary subgroups; this bounds the number of conjugacy classes of homomorphisms into the group.
  several-ended-groups-act-fixed-point-freely-on-trees: that is Stallings' theorem, one input of the one-endedness step; this is the Paulin/Bestvina limiting argument in its relatively hyperbolic form.
artifacts:
  - research/fa-groups-finitely-many-homs-to-rel-hyperbolic-groups-citation.md
---

**ESTABLISHED** by import: `fa-groups-finitely-many-homs-to-rel-hyperbolic-groups-citation`.

**(DS) Drutu--Sapir, Corollary 4.37.** Let `Λ` be a finitely generated group with Serre's
property FA. Let `H` be an infinite, finitely generated group that is (strongly) relatively
hyperbolic with respect to a finite family of finitely generated peripheral subgroups
`H_1, ..., H_m`, each different from `H`. Then there are only finitely many homomorphisms `Λ → H`,
pairwise non-conjugate in `H`, whose image is not parabolic. Here parabolic means contained in a
conjugate of some `H_i`.

A word-hyperbolic group is hyperbolic relative to the trivial subgroup (Drutu--Sapir, Remark 1.13).
Then "non-parabolic" means "nontrivial image".

**(L) Levitt, Theorem 1.4.** A one-ended hyperbolic group `G` has `Out(G)` infinite if and only if
`G` splits over a virtually cyclic subgroup with infinite center, either as an arbitrary HNN
extension or as an amalgam of groups with finite center.

(L) independently confirms the hyperbolic case of the consequence that the consumers use.

**Consumer.** `rel-hyperbolic-hosts-make-witness-powers-host-inner`.
