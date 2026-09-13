---
rg: 2
id: promislow-radius4-support-pairs-need-zeta8
kind: claim
title: A characteristic-zero field supports a nontrivial unit on a radius-four census pair only if it contains zeta_8
distinct_from:
  gardam-support-pair-has-no-rational-units: that is Gardam's one support pair; this covers the support pairs of all 52 units of F_2[P] supported in the word ball of radius four.
  promislow-radius4-one-sided-and-integral-separation: that counts the units of F_2[P] supported in B(4) and lifts their nontrivial residues to Z; this fixes the support and inverse support of each such unit and determines which characteristic-zero fields have units on them.
  unit-conjecture-fails-over-complex-numbers: that imports the existence of nontrivial complex units; this determines which characteristic-zero fields have units on 52 support pairs.
  support-pair-unit-scheme-is-finite-over-z: that shows the units on any support pair form a scheme finite over Z; this computes the characteristic-zero points of that scheme on 52 pairs.
  rational-unit-conjecture-torsion-free: that is the unit conjecture over Q for every torsion-free group; this is 52 support pairs on one group.
---

**ESTABLISHED.** Let `P` be the Promislow group, and let `B(4)` be its word
ball of radius four in the generators `a, b`. Let `u_0 in F_2[P]` be a
nontrivial unit with support in `B(4)`. There are 52 of them
(`promislow-radius4-one-sided-and-integral-separation`), and each has a
21-element support. Put `S = supp(u_0)` and `T = supp(u_0^(-1))`.

Let `K` be a field of characteristic zero, and let `u in K[P]` be a unit with
`supp(u) in S` and `supp(u^(-1)) in T`. If `u` is not `lambda g`, then `K`
contains a primitive eighth root of unity.

So no nontrivial unit of `Q[P]`, `R[P]`, `Q_2[P]` or `Z[P]` has support in
`S` and inverse support in `T`. Conversely, every field containing `zeta_8`
has a nontrivial unit on each of the 52 pairs. Over `Qbar` each pair carries
exactly 16 nontrivial units up to scaling. They are the twists
`sum chi(g) u_g g` of one of them by the 16 characters `chi: P -> mu_4`, and
all their coefficients are eighth roots of unity.

This extends `gardam-support-pair-has-no-rational-units` from one pair to all
52. The inverse support is fixed to `T`. A unit of `K[P]` supported in `S`
whose inverse is supported elsewhere, even inside Tabei's 155-element box, is
not covered. Neither are units of `Q[P]` supported in `B(4)` whose support is
not one of the 52 supports, nor anything at radius five.

DERIVATION
[[promislow-radius4-support-pairs-need-zeta8-proof]]
