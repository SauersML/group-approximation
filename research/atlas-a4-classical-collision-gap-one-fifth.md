---
rg: 2
id: atlas-a4-classical-collision-gap-one-fifth
kind: claim
title: Collision 19243 forces a one-fifth A4-context failure rate on every classical chart alignment
artifacts:
  - experiments/atlas_triangle_19243_classical_gap.py
  - experiments/atlas-word-19243.json
distinct_from:
  atlas-a4-holonomy-coherence-gap: that is the matrix-valued amplified theorem needed for nonhyperlinearity; this is its exact finite classical soundness calibration over chart automorphisms.
---

Consider either automorphism coset of `A8=GL(4,2)`: inner alignments

```text
x |-> A x A^-1
```

or outer alignments obtained by composing with inverse-transpose.  Among the
`20160` alignments in either coset, restrict to those for which collision word
`19243` evaluates to the identity.

Then every such alignment violates at least six of the thirty shortest A4
pair-cube contexts.  Equivalently, conditioned on perfect collision acceptance,
the classical triangle packet has soundness at most

```text
24/30 = 4/5.                                           (A4-CLASSICAL-GAP)
```

The bound is sharp: in each automorphism coset exactly four alignments violate
only six contexts.  There are `2880` collision-perfect alignments per coset.

Thus the finite packet has a genuine constant-gap PCP interpretation already at
the classical normalizer level.  The remaining amplified problem is not to
find frustration—it is to prove a matrix-valued agreement/rounding theorem
which turns an exact regular A4 coherence network into a direct-sum mixture of
these classical chart alignments (or otherwise transfers this `1/5` gap).
