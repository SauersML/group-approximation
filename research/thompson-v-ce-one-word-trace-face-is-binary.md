---
rg: 2
id: thompson-v-ce-one-word-trace-face-is-binary
kind: claim
title: One nontrivial word of Thompson V has a binary Connes-embeddable support value
distinct_from:
  cyclic-carrier-energy-stability: that asks equality of one support functional on the CE and finite-dimensional trace cones for an arbitrary group; this computes the only two possible CE support values for the elementary positive word polynomial of bare Thompson V.
  rcc-carrier-character-face-compression: that studies a constrained face of characters of an HNN carrier; this uses the complete character simplex of V and has no HNN extension or relative commutant.
  thompson-clifford-central-product-tape: that uses V to address an infinite Clifford tape; this uses no tape, Clifford packet, central involution, or multiplicity decoder.
---

Fix any `w!=1` in Thompson's group `V` and set

```text
q_w=(1-w)^*(1-w) in C[V]_+.
```

If `T_CE(V)` is the set of traces whose GNS von Neumann algebras are Connes
embeddable, then

```text
sup_(tau in T_CE(V)) tau(q_w) is either 0 or 2.            (TV1)
```

The second case occurs exactly when `V` is hyperlinear. Thus any strict
upper bound below `2` automatically improves to the exact finite-dimensional
ceiling `0` and proves `V` nonhyperlinear.

The bare implication "strictly below `2` implies nonhyperlinear" already
follows for any simple group: a nontrivial homomorphism into a tracial matrix
ultraproduct is injective, and then the regular trace is matricial. The
Dudko--Medynets input adds the exact zero-or-two support law and the complete
interval description of CE trace values; it does not by itself make the
strict ceiling easier.

This is a new specialization/reduction of the published character
classification, not a proof that the strict upper bound holds. The same
character/corner maneuver already appears informally in the repository for a
Thompson subgroup of the Leavitt construction; `(TV1)` packages its bare-`V`,
one-positive-element consequence in the Cairn graph.
