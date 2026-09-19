---
rg: 2
id: atlas-a4-two-context-collision-gap
kind: claim
title: Collision 19243 plus two A4 contexts already has classical conditional soundness one-half
artifacts:
  - experiments/atlas_triangle_19243_two_context_gap.py
  - experiments/atlas-word-19243.json
distinct_from:
  atlas-a4-classical-collision-gap-one-fifth: that uses all thirty shortest A4 contexts and counts at least six failures; this claim extracts a two-context hitting core from the same finite audit.
---

Let `q=q_19243`.  Among the thirty packet contexts of
`atlas-shortest-a4-triangle-packet`, take the two spanning-tree kernel words at
indices

```text
6910, 6940.
```

Write them as `u` and `v`.  They are pair-cubes `(b_2 a_1)^3` with the
following factor-two involutions and factor-one order-three elements:

```text
u:
  b = 01000000010100000000010000000001
  a = 01010000010000000000010000000001

v:
  b = 01010000000100000000010000000001
  a = 00010000010100000000010000000001
```

For every inner or outer automorphism alignment of `A8=GL(4,2)` satisfying
`q=1`, at least one of `u,v` is nontrivial.  More precisely, in **each**
automorphism coset there are `2880` collision-perfect alignments, with exact
failure histogram

```text
exactly one of {u,v} fails : 1152
both u and v fail          : 1728
neither fails              : 0.
```

Hence conditioned on perfect collision acceptance, the two-context verifier
has classical soundness at most `1/2`; the bound is sharp because the first
class is nonempty.

The key reduction is not merely numerical.  The full thirty-query classical
PCP has a two-query hitting core.  Any amplified argument may therefore focus
on the trace moments of just `u`, `v`, and `q` rather than synchronizing all
thirty A4 contexts at the final soundness step.

## Attempts

- The exact finite enumeration is implemented in
  `experiments/atlas_triangle_19243_two_context_gap.py`; the proof route records
  why that exhaustive audit is a complete certificate for both automorphism
  cosets.
