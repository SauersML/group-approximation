---
rg: 2
id: virtually-torsion-free-infinite-mf-radical-gives-seed
kind: claim
title: A virtually torsion-free recursively presented group whose MF radical escapes its finite radical yields a torsion-free finitely presented non-MF group
distinct_from:
  full-mf-radical-seed-has-no-torsion-free-quotient: that is a homomorphic-image obstruction, since a torsion-generated full radical dies in every torsion-free quotient; this passes to a finite-index subgroup instead of a quotient, and finite-index passage keeps an infinite radical alive.
  torsion-free-central-cover-forces-abelian-finite-subgroups: that kills central covers of a torsion host; this uses no cover at all, only the finite-index trace of the radical.
  corona-finite-index-radical-heredity: that is the general trace formula; this is its consequence for virtually torsion-free hosts, with the finite-radical dichotomy and the Higman step that turns it into the torsion-free seed.
artifacts:
  - research/corona-finite-index-radical-heredity.md
  - research/torsion-free-higman-embedding.md
---

**ESTABLISHED, NO PROPERTY `(T)`.**  Let `H` be a finitely generated,
recursively presented, virtually torsion-free group.  Let `W(H)` be the union
of all finite normal subgroups of `H`.  Fix a torsion-free subgroup `E` of
finite index `m`.  Then `W(H)` is a finite normal subgroup of order at most
`m`.

**Dichotomy.**  Exactly one of the following holds.

1. `Rad_MF(H) <= W(H)`.  In this case `Rad_MF(H)` is finite, and
   `Rad_MF(E) = 1` for every torsion-free finite-index `E`.
2. `Rad_MF(H)` is not contained in `W(H)`.  In this case `Rad_MF(H)` is
   infinite, and every torsion-free finite-index `E <= H` is finitely
   generated, recursively presented and not MF.  `E` embeds in a finitely
   presented torsion-free group `T` that is not MF.  Such a `T` is an instance
   of `property-t-free-torsion-free-fp-non-mf-seed`, and its proof uses no
   Property `(T)` beyond whatever proves the hypothesis on `H`.

**Converse.**  Every seed `T` is itself such an `H`, with `E = T` and
`W(T) = 1`.  So the torsion-free seed is *equivalent* to the existence of a
f.g., recursively presented, virtually torsion-free group whose MF radical is
not contained in its finite radical.

**Corollary (corner form).**  Suppose `H` is as above and `K <= H` is a finite
subgroup with `K` not contained in `W(H)`, equivalently with infinite normal
closure.  Suppose also that a unital star map from an algebra with no
Connes-embeddable trace lands in the augmentation corner `q_K C[H] q_K`.  Then
`nonhyperlinear-finite-augmentation-corner-kills-mf` gives `K <= Rad_MF(H)`,
so case 2 holds and the seed exists.  Normality of `K` is not needed anywhere.

This is exactly the gate the countermodel `Rad^#` of
`torsion-free-seeds-need-kernel-descent-or-trace-corner` isolates.  A torsion
conclusion, here the corner rule, is combined with the finite-index trace
rule.

## Attempts

- 2026-09-18 (swarm-0917-w12-w12-ptm-last1): proved in the proof route.  The
  only caveat is structural.  The binary-Leavitt Steinberg host `St_20(L)` has
  no proper finite-index subgroups, and it is not virtually torsion-free since
  `x_12(1)` is an involution.  So this lemma is useless on that host.  A usable
  host must also be non-MF, and in particular not residually finite.  That
  excludes every finitely generated linear group (Malcev), every virtually
  special group and every lattice in a linear Lie group.  The remaining
  natural hosts are virtually torsion-free groups that are not residually
  finite.  Examples are finite extensions of irreducible lattices in products
  of trees (Burger--Mozes, Wise), and Deligne-type central extensions of
  arithmetic groups.  The Deligne type is excluded here because it is Kazhdan.
