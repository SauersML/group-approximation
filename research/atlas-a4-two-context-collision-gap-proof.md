---
rg: 2
id: atlas-a4-two-context-collision-gap-proof
kind: route
title: Exhaust the two automorphism cosets and certify the two-context hitting set
target: atlas-a4-two-context-collision-gap
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_triangle_19243_two_context_gap.py
  - experiments/atlas-word-19243.json
---

The completeness reduction is the same finite one used by the established
thirty-context audit.  Every automorphism of `A8=GL(4,2)` is either inner or
inverse-transpose followed by an inner automorphism, and each coset is
parameterized by the `20160` matrices `A in GL(4,2)`.

`experiments/atlas_triangle_19243_two_context_gap.py` reconstructs the complete
radius-five kernel window and the certified thirty-context packet.  It asserts
that packet positions `0` and `4` are still the spanning-tree words `6910` and
`6940`, so the certificate fails loudly if packet enumeration changes.

For each of the `20160` inner and `20160` outer alignments it evaluates
collision `19243` exactly over `F2`.  In each coset exactly `2880` alignments
satisfy the collision.  On those survivors it evaluates only the two selected
pair-cubes.  The exact histogram in each coset is

```text
1 failed selected context : 1152
2 failed selected contexts: 1728
0 failed selected contexts:    0.
```

The script asserts this entire histogram, not just the minimum.  Therefore no
collision-perfect classical alignment satisfies both selected A4 contexts,
and the `1152` one-failure alignments show that the conditional soundness
`1/2` is sharp for this two-query core.
