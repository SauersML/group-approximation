---
rg: 2
id: boone-higman-type-a-class-closed-under-finite-extensions
kind: claim
title: The permutational Boone--Higman class is closed under finite direct products and finite-index overgroups
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that gives a finitely presented simple envelope to the subgroups of one actor; this is the known closure of the class of such subgroups under finite direct products and finite-index overgroups.
  aut-free-groups-satisfy-permutational-boone-higman: that imports the Aut(F_n) theorem and, in its body, closure of the same class under free products; this is closure under finite direct products and finite-index overgroups.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is one source of inputs, finitely presented self-similar groups, through Rover--Nekrashevych commutator subgroups; this is a permanence property of the type (A) route and does not assert that self-similar groups carry type (A) actions.
artifacts:
  - research/artifacts/bh-type-a-permanence-2026-09-12.md
---

Let `B_A` be the class of groups that embed in some group admitting an action
of type (A), as defined in `type-a-action-gives-boone-higman-for-subgroups`.
In the language of Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2,
these are the groups satisfying the permutational Boone--Higman property.

**Credit: known.** BFFHZ state that the property "is stable under commensurability
and direct products", citing Zaremsky, arXiv:2405.18354, Proposition 5.6. Their
Corollary F adds closure under free products, imported in
`aut-free-groups-satisfy-permutational-boone-higman`. The derivation attached
here is an elementary verification, and no priority is claimed.

1. `B_A` is closed under subgroups and finite direct products.
2. `B_A` is closed under finite-index overgroups: if `H <= G` has finite index
   and `H` is in `B_A`, then `G` is in `B_A`.
3. Every group in `B_A` embeds in a finitely presented simple group. Every
   finitely generated group in `B_A` has solvable word problem.

Consequently, if some finite-index subgroup of `G` embeds in
`Gamma_1 x ... x Gamma_m`, where each `Gamma_j` admits an action of type (A),
then `G` satisfies the Boone--Higman conjecture.

**Scope.** Two things are not claimed.
- **Outside B_A:** closure of the Boone--Higman class itself under direct
  products or finite extensions. For example, a product of two finitely
  presented simple groups is covered only when both lie in `B_A`.
- **Known classes:** which already-known classes lie in `B_A`. Cairn establishes
  it for finitely presented full Cantor groups containing standard V
  (`fp-full-binary-cantor-groups-have-type-a-actions`) and records the strongly
  shift-similar case (`fp-strongly-shift-similar-admits-type-a-action`). Whether
  the hyperbolic, contracting self-similar or `GL_n(Q)` envelopes of the
  literature pass through a type (A) actor has not been checked here.

The derivation is `type-a-class-finite-extensions-proof`.
