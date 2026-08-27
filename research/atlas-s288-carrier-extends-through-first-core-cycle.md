---
rg: 2
id: atlas-s288-carrier-extends-through-first-core-cycle
kind: claim
title: The structural S288 carrier extends through the first additional core cycle on 576 points
artifacts:
  - experiments/atlas_a4_regular_amalgam_finite_search.py
  - experiments/atlas_a4_s576_first_cycle_amalgam.py
  - research/artifacts/atlas-a4-s576-first-cycle-amalgam.json
  - research/atlas-s288-carrier-extends-through-first-core-cycle-proof.md
distinct_from:
  atlas-first-post-a10-edge-has-no-degree-ten-completion: that rules out the next edge inside the A10/S10 carrier; this changes the local carrier and constructs an exact positive completion.
  atlas-forward-collision-has-faithful-s288-amalgam: that stops before the missing first-chart involution and next A4 edge; this adjoins both while preserving collision and the forward carrier.
  atlas-first-post-a10-core-edge-is-a-centralizer-double-coset: that isolates a large regular-alignment problem; this solves the corresponding edge by a small structural regular amalgam.
---

The structural `A4 x A4` forward-collision carrier has an exact finite
extension through the next distinct large-component core pair

```text
first s  ->  second r^-1.
```

More precisely, there is a finite permutation group `Q_1<=S_576` containing
faithful copies of

```text
the 144-state forward carrier,
the first local S3 x S3       (order 36),
the collision S3 x C2        (order 12),
the new A4 edge               (order 12).
```

The missing first involution is the negative factor-swap automorphism of
`A4 x A4`.  It and the second order-three label close inside an
`S4 x C2` block.  The two finite sides share a labeled `C2^3`, and their
regular actions match on 576 points.

Thus the first cycle is a genuine obstruction for the A10 carrier but not for
the structural carrier.  Remaining core edges are not asserted here.
