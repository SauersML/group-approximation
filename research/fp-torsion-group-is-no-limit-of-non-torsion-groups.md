---
rg: 2
id: fp-torsion-group-is-no-limit-of-non-torsion-groups
kind: claim
title: A torsion limit of surjections through infinitely many groups with elements of infinite order is not finitely presented
distinct_from:
  fp-direct-limit-of-surjections-stabilizes: that is the general stabilization lemma for finitely presented direct limits; this is its consequence for torsion limits, the fence against limit constructions in Zaremsky Problem 1.11
---

Let `H_0` be finitely generated, and let `H_0 -> H_1 -> H_2 -> ...` be
surjections with direct limit `G`. Suppose `G` is a torsion group and
infinitely many `H_i` contain an element of infinite order. Then `G` is not
finitely presented.

**What it fences.** Many constructions of infinite torsion groups add
relators in infinitely many steps. Every stage visibly has elements of
infinite order, for instance a non-elementary hyperbolic group, and torsion
appears only in the limit. No construction of this shape can give a
finitely presented torsion group, so none can answer Zaremsky Problem 1.11
positively. Equivalently, a finitely presented torsion group `G` is already
torsion at a finite stage of *every* sequence of quotients of a finitely
generated group that converges to `G`.

**Scope.** The fence needs only that infinitely many stages have an element
of infinite order. It says nothing about constructions whose stages are
eventually torsion. It also leaves alone constructions that are not limits
of quotients of one finitely generated group.

**Model test.** A finite group `G` is finitely presented. So along any
sequence of surjections converging to `G`, only finitely many stages can
contain an element of infinite order. By
`fp-direct-limit-of-surjections-stabilizes` the stages are eventually
isomorphic to `G`, which agrees with this claim.

Proof: `fp-torsion-group-is-no-limit-of-non-torsion-groups-proof`.
