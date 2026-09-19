---
rg: 2
id: block-escape-nonsoficity-proof
kind: route
title: Pass invariant subset blocks to intermediate coset wreath quotients
target: block-escape-relocates-nonsoficity
requires: []
---

Let a transitive finite `K`-set `Y` admit a nontrivial invariant partition,
and suppose every subset in the orbit `O` is a union of blocks.  Any
permutation acting inside each block fixes every member of `O` but can move
all points of `Y`.  Thus no modulus can infer sitewise fixedness from
set-orbit fixedness.

At zero error, if the indicator vectors of `O` span `F_2^Y`, then a
permutation fixing them all fixes the standard basis and is the identity.
Hence total failure requires a proper invariant indicator subspace; block
systems are its geometric model.

For `X=G/Gamma`, invariant blocks correspond to intermediate subgroups
`Gamma<=H<=G`.  The quotient `G/Gamma -> G/H` induces

```text
(directSum_(G/Gamma) C_2) semidirect G
  -> (directSum_(G/H) C_2) semidirect G.
```

The marked lamp difference maps to `a_(hH)a_H`, which remains nontrivial
exactly when `h notin H`.  Since the original mark lies in the sofic radical,
its nontrivial image forbids the quotient wreath product from being sofic.
If the quotient action were sofic, the standard generalized-wreath closure
theorem would make that wreath product sofic, a contradiction.  Therefore
every mark-separating block quotient inherits nonsoficity.
