---
rg: 2
id: centerless-fp-finitely-many-conjugacy-classes-gives-pbh
kind: claim
title: A finitely presented group with trivial center and finitely many conjugacy classes satisfies permutational Boone--Higman
distinct_from:
  fiber-product-conjugation-action-lemma: that computes the pair-orbits of a two-sided translation action in the fiber-product setting and finds conjugacy classes, generally many; this uses the same count for G x G acting on G, where finitely many classes make the action type (A).
  osin-torsion-free-two-conjugacy-class-groups-exist: that imports finitely generated groups with two conjugacy classes, which are not finitely presented; this needs a finitely presented group with finitely many classes, which is not known to exist in the infinite case.
  pbh-passes-to-relative-free-group-automorphisms: that moves the permutational property to Aut_H(H * F_n) for n >= 2; this is the rank-one situation BFFHZ discuss after their Observation 2.4, realized through G x G instead of Aut_G(G * F_1).
artifacts:
  - research/artifacts/type-a-invariants-2026-09-13.md
---

**ESTABLISHED** through `centerless-finite-conjugacy-classes-pbh-proof`. Not
independently reviewed. Elementary; no novelty claimed.

## Statement

Let `G` be a finitely presented group with trivial center and finitely many
conjugacy classes. Then `G x G` acting on `G` by `(a,b)·x = a x b^-1` is of type
(A). So `G ≅ G x 1` satisfies permutational Boone--Higman. If `G` is simple, it
embeds in a finitely presented simple MIF group, so BFFHZ Question 3.4 holds for
`G`.

## Context

- **BFFHZ's remark.** BFFHZ (arXiv:2503.21882v2, text on MSI
  `/scratch.global/sauer354/bh-outfn-mcg/2503.21882v2.txt`, l.376--381) discuss the
  rank-one action of `Aut_G(G * F_1)` on `Hom_G(G * F_1, G)`: "we would need G to
  have finitely many conjugacy classes: this is certainly not always the case (and
  it is an open question whether it can ever occur for a finitely presented
  infinite G)."
- **What this adds.** The converse direction for a different actor: finitely many
  conjugacy classes already suffice, with `G x G` in place of the automorphism
  group.
- **Scope.** The hypothesis is not known to hold for any infinite finitely
  presented group. The claim is recorded as the exact sufficient condition. A
  finitely presented simple group with finitely many conjugacy classes cannot be a
  counterexample to Question 3.4 (`q34-counterexample-necessary-conditions`).
