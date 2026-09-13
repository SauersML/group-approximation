---
rg: 2
id: left-right-sofic-closed-under-co-amenable-overgroups
kind: claim
title: A group with a co-amenable left-right sofic subgroup is left-right sofic
distinct_from:
  mikhailova-left-right-action-sofic-for-lea-quotients: that builds models from local embeddings into amenable groups; this passes soficity of the left-right action up from a co-amenable subgroup, with no approximation of the quotient itself.
  sofic-actions-restrict-to-co-amenable-subgroups: that is the general restriction principle for any action; this applies it to the left-right action, whose restriction to the preimage of a co-amenable subgroup splits into double-coset orbits handled by the Goursat reduction.
  uas-base-gives-sofic-hnn-coset-action: that makes the coset action G/Gamma of an ascending HNN extension sofic over a universally action-sofic base; this makes the left-right action of an ascending HNN extension sofic over a left-right sofic base.
artifacts:
  - research/artifacts/pfg-positive-goursat-reduction-2026-09-13.md
---

ESTABLISHED (unreviewed). "Left-right sofic" is defined in
[[product-free-set-actions-reduce-to-left-right-actions]].

**Theorem.** Let `P <= H` be co-amenable. If `P` is left-right sofic, so is
`H`. Hence `H` is left-right sofic iff some co-amenable subgroup is, iff every
co-amenable subgroup is.

**Corollaries.**

1. Left-right sofic-by-amenable groups are left-right sofic.
2. An ascending HNN extension `< B, t | t b t^-1 = theta(b) >` of a left-right
   sofic base `B` is left-right sofic. The kernel onto `Z` is an increasing
   union of copies of `B`.
3. Groups with a co-amenable LEA subgroup are left-right sofic. This includes
   amenable extensions of LEA groups and ascending HNN extensions of LEA
   groups. It is not settled here whether this produces a finitely presented
   group outside LEA, i.e. one that is not residually amenable.

**Firewall (property (T)).** In a Kazhdan group every co-amenable subgroup has
finite index. So the theorem adds nothing for the fixed nonsofic property-(T)
quotient of [[mikhailova-left-right-action-current-frontier]], or for any host
without infinite amenable transitive actions.

**Firewall (soficity).** All groups reached from amenable groups by
subgroups, products, marked limits and co-amenable overgroups are sofic, by
(G) of [[sofic-actions-restrict-to-co-amenable-subgroups]]. A positive answer
for a nonsofic quotient needs models in which kernel words act nontrivially,
as (MCC4) of [[mikhailova-left-right-soficity-is-one-color-code]] requires.

**Mechanism.** Put `A_i = q_i^-1(P)`. Then `A_1 x A_2` is co-amenable in
`F x F'`. Its orbits on `H` are the double cosets `PhP`, whose stabilizers have
Goursat quotient `P ∩ hPh^-1`. Apply the Goursat reduction orbitwise, then
co-amenable restriction.

DERIVATION [[left-right-sofic-closed-under-co-amenable-overgroups-proof]].
