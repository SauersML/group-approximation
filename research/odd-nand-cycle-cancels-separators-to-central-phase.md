---
rg: 2
id: odd-nand-cycle-cancels-separators-to-central-phase
kind: claim
title: An odd NAND swap cycle cancels every separator and leaves a bare central phase word
distinct_from:
  nand-sheet-swap-cannot-be-a-pure-central-phase: that proves one local swap gives JSR rather than JR; this shows the separator contamination cancels globally in cyclic order.
  s4-nand-cycle-holonomy-is-one-s2-bit: that records whether atom matchings swap around a finite chart cycle; this computes the ordinary corner word carried by a directed cycle of local swaps.
  boolean-predicate-central-phase-word: that asks for a phase-safe predicate compiler in general; this supplies the exact phase word for an odd cycle of three-point NAND predicates, conditional only on the local swap transports.
---

Let `q` be a corner unit, let `J` be a central involution in the corner, and
let

```text
X_1,...,X_n,             X_(n+1)=X_1
```

be self-adjoint involutions such that `[X_i,X_(i+1)]=0`.  Suppose each
adjacent pair is represented on the three NAND atoms and has a corner unitary
`H_i` implementing the plus-sheet swap which fixes `X_i`.  Equivalently, by
`nand-sheet-swap-cannot-be-a-pure-central-phase`,

```text
H_i X_(i+1) H_i^* = J X_i X_(i+1).                    (ONC1)
```

Define the cyclic word

```text
W_C=product_(i=1)^n (H_i X_(i+1) H_i^*)               (ONC2)
```

with the factors in cyclic order.  Then

```text
W_C=J^n.                                                (ONC3)
```

In particular, for an odd cycle,

```text
W_C=J,                                                   (ONC4)
```

so the separator-contaminated local lifts combine to a **bare central marked
word**.  No commutation between nonadjacent variables or between different
transport unitaries is used.

This is a phase-safe word compiler, not by itself a gap.  The left side of
`(ONC2)` is not automatically the identity; the exact finite signed-packet
models realize `(ONC4)` with `J=-q`.  To obtain a nonhyperlinear group from
this word, the global no-CE construction must still place all local NAND
contexts and their `H_i` in one algebraic group corner while ensuring that
finite-dimensional approximate models cannot retain the marked phase.  The
new point is that no residual readable/separator sign remains after an odd
cycle: the mark-return algebra is complete once that common-corner placement
is achieved.

