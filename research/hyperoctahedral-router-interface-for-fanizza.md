---
rg: 2
id: hyperoctahedral-router-interface-for-fanizza
kind: claim
title: A common finite-type router would compile every Fanizza predicate by one balanced word
distinct_from:
  fanizza-shared-multiplicity-predicate-circuit-cell: that asks to cancel two independent controlled-gate multiplicities; this replaces the nonlinear circuit by one router and an exact arbitrary truth-table word, leaving only preservation of the larger constant packet.
---

OPEN.  For each bounded Fanizza context, use one common signed-permutation
packet `B_N`, its Pauli subgroup, and one router `c`.  The selector covariance
relations on the Pauli generators make the restriction of `c` to assignment
sector `a` equal to

```text
tau_a tensor V_a
```

by Schur's lemma.  If the constants in the word from
`hyperoctahedral-balanced-word-truth-table` act as `g tensor I` on the same
carrier, the balanced word cancels `V_a` and its relation `W_F(c)=1` kills
exactly the forbidden sectors.  Using one packet and a different router for
each context keeps all original BCS involutions on one common multiplicity
space, so the local penalties assemble into the Fanizza state.

The remaining assertion is a finite-type return:

```text
Pauli covariance + defining relators
  => the whole B_N constant packet acts trivially on external multiplicity,
     up to a computable dimension-free HS error.        (HRI1)
```

It is not automatic.  Covariance fixes only the irreducible Pauli action;
constants outside the Pauli normalizer can move or multiply its isotypic
carrier.  This is the exact point at which the otherwise complete balanced
lookup construction still needs a Schur/Hecke return mechanism.

`right-regular-covariance-forces-one-common-router` now removes the router's
coordinate-dependent gauge completely.  Enlarge the fixed packet by a right
regular copy of a finite group `L`, make the router commute with it, and use a
finite family of `A`-equivariant sign colorings.  On every selector sector the
router is then, robustly and with a dimension-free computable constant,

```text
lambda(a) tensor V_a
```

with one common `V_a`, rather than one unrelated gauge per coordinate.  What
remains of `(HRI1)` is strictly smaller: the non-Pauli constants used by the
balanced truth-table word may themselves carry a finite-group representation
on this multiplicity space, and `V_a` need not commute with that second-layer
action.  A final packet must either isolate its trivial type or cancel those
multiplicity commutators.  The coordinate-gauge problem is no longer part of
the frontier.

`second-layer-lookup-cancellation-no-go` shows
that merely replacing `W_F` by a longer or more cleverly balanced word cannot
finish the job.  If a word vanished for an arbitrary representation of the
constant packet together with an arbitrary router multiplicity, its element
in the free product `B_N*Z` would be trivial, and the same word could not
evaluate to `z` in the finite truth packet.  The remaining move must therefore
be genuine **type selection or multiplicity coupling**, not word-level
cancellation.

On the HALT side no trace preservation is needed: tensor the Fanizza GNS
model with the natural packet, take `c` to be the selector-controlled
translation, and `(HBT3)` makes every predicate relator exact.  For a
universal embedded finite control, choose for each context an allowed anchor
assignment; sending every BCS variable to `1` and its router to the anchor
translation gives a retraction onto the constant packet.  Thus only the
finite-matrix decoder `(HRI1)`, not exact completeness or algebraic packet
survival, remains.
