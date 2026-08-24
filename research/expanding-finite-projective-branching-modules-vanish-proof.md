---
rg: 2
id: expanding-finite-projective-branching-modules-vanish-proof
kind: route
title: Convert module decompositions into the exact corona branching equation
target: expanding-finite-projective-branching-modules-vanish
requires:
  - exact-corona-branching-dimension-collapse
  - corona-projective-hilbert-hotel-cancellation
---

Choose stable projections `p_i` with

```text
P_i=p_i Q_d^(k_i).
```

An isomorphism of finitely generated projective modules is equivalent to
Murray--von Neumann equivalence of their stable defining projections.  Thus
`(EPM1)` gives

```text
[p_i]=sum_j a_ij [p_j] in V(Q_d).                       (EPP1)
```

Choose partial isometries implementing the module isomorphisms.  Their range
projections give an exact `A`-branching system after one common stable
amplification.  The theorem
`exact-corona-branching-dimension-collapse` applied with `(EPM2)` gives
`p_i=0` for every `i`, hence `(EPM3)`.

For `(EPM4)`, the orthogonal vertex idempotents sum to the identity of the
branching algebra.  Their images split

```text
P=directSum_i v_iP.
```

The branch generators and their reverse maps implement `(EPM1)` on these
summands.  Therefore all summands vanish and so does `P`.

If an irreducible component is closed, every decomposition row indexed by
that component uses only modules from the same component.  Its principal
block is therefore an exact branching subsystem, and the preceding proof
applies to it unchanged.  Finally, substituting the direct-sum formula for each `P_j`
into the formula for `P_i` counts `sum_j a_ij d_jk=(AD)_ik` copies of `P_k`,
which proves the composition statement.
