---
rg: 2
id: atlas-a4-classical-collision-gap-one-fifth-proof
kind: route
title: Exhaust all inner and outer A8 chart alignments and count failed A4 contexts
target: atlas-a4-classical-collision-gap-one-fifth
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_triangle_19243_classical_gap.py
  - experiments/atlas-word-19243.json
---

The search space is finite and exact.  Every automorphism of
`A8=GL(4,2)` is either inner or inverse-transpose followed by an inner
automorphism.  Thus each coset is parameterized by the `20160` matrices
`A in GL(4,2)`.

For every alignment, evaluate collision `19243` exactly over `F2`.  There are
`2880` collision-perfect alignments in each coset.  For each of those, evaluate
the thirty certified pair-cubes.  Since a pair-cube repeats its first two
syllables three times, its test is exactly whether the corresponding aligned
matrix product has cube equal to `I`.

`experiments/atlas_triangle_19243_classical_gap.py` performs these calculations
using only exact `F2` matrix multiplication and inversion.  In both automorphism
cosets the conditioned failure histogram begins

```text
6 failures : 4 alignments
7 failures : 16 alignments
8 failures : 4 alignments
...
```

and contains no entry below six.  The script asserts both the `2880` collision
survivors and the minimum `6`, so a change in the finite certificate fails
loudly.  Therefore every collision-perfect classical alignment violates at
least `6/30=1/5` of the A4 contexts, and the four minimizers show sharpness.
