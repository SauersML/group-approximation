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

On the HALT side no trace preservation is needed: tensor the Fanizza GNS
model with the natural packet, take `c` to be the selector-controlled
translation, and `(HBT3)` makes every predicate relator exact.  For a
universal embedded finite control, choose for each context an allowed anchor
assignment; sending every BCS variable to `1` and its router to the anchor
translation gives a retraction onto the constant packet.  Thus only the
finite-matrix decoder `(HRI1)`, not exact completeness or algebraic packet
survival, remains.
