---
rg: 2
id: atlas-forward-collision-a10-absorbs-both-full-charts
kind: claim
title: The faithful A10 forward-collision carrier absorbs both full A8 chart vertices
artifacts:
  - experiments/atlas_a4_a10_full_chart_regular_extension.py
  - research/artifacts/atlas-a4-a10-full-chart-regular-extension.json
  - research/atlas-forward-collision-a10-absorbs-both-full-charts-proof.md
distinct_from:
  atlas-forward-collision-has-faithful-a10-quotient: that embeds only the minimal local vertex groups F,C,K; this adjoins faithful copies of both complete A8 chart groups while retaining the same local A10 carrier.
  atlas-14-core-q19243-gl5-countermodel: that realizes all fourteen cross-chart core edges but no forward central edge; this realizes the forward edge and collision together with both internal chart groups but does not impose the remaining cross-chart edges.
  atlas-one-forward-c3-has-no-standard-gl6-completion: that fixes two standard padded binary-linear chart embeddings; this uses regular permutation amplifications and independent subgroup alignments.
---

There is a finite permutation group `P<=S_(1814400)` containing faithful
copies of

```text
A10,       A8^(0),       A8^(1)
```

such that `A8^(0)` agrees with the A10 carrier on the labeled
`F~=C3 x S3`, while `A8^(1)` agrees with it on the labeled collision
`K~=S3`.  Consequently `P` realizes both full internal A8 chart dictionaries
together with collision `19243`, the forward central edge, and the adjacent
core edge already present in the faithful A10 quotient.

The construction uses the left regular A10 action and ninety regular copies
of each A8 action.  Their restrictions to `F` and `K` have identical labeled
regular multiplicities, so exact permutation conjugators align them.

This does not impose any further cross-chart pair-cube.  The first additional
distinct core pair is the first cycle-holonomy constraint, rather than another
tree-of-finite-groups inclusion.
