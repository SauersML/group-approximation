---
rg: 2
id: corona-quotients-program-countable-graph-completions-proof
kind: route
title: Kill exactly the selected pair-support blocks
target: corona-quotients-program-countable-graph-completions
requires:
  - pauli-support-realizes-boolean-word-calculus
  - matrix-corona-projection-ideal-and-corner-calculus
---

Use the Pauli construction with a disjoint infinite block `C_e` for every
nonedge and a disjoint private infinite block for every vertex.  Equation
`(GC1)` is the Boolean commutator-support formula.

An element becomes one modulo `I_F` exactly when its support ideal is
contained in `I_F`.  Since the `C_e` are pairwise disjoint and infinite,

```text
J_(C_e)<=I_F iff e in F.
```

Thus precisely the commutators indexed by `F` vanish in the quotient, proving
`(GC2)`.  Private blocks are disjoint from the union defining every `I_F`, so
each vertex involution remains nonidentity.

If `F!=F'`, an edge in their symmetric difference contributes an entire
infinite block contained in one support union and disjoint from the other.
The projection-ideal comparison theorem therefore gives `I_F!=I_(F')`.
Almost-inclusion of support unions is exactly inclusion of the indexing
subsets, proving the order embedding.
