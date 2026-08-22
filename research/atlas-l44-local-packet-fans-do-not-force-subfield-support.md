---
rg: 2
id: atlas-l44-local-packet-fans-do-not-force-subfield-support
kind: claim
title: Local Atlas packet fans do not force the L4(4) subfield frame
artifacts:
  - experiments/atlas_a4_l44_fan_escape.py
distinct_from:
  atlas-cfsg-family-split-does-not-finitize-a8-carriers: that exhibits an unbounded carrier tower without testing relations; this gives exact relation-satisfying nonsubfield local frames at its first multiplicity-two endpoint.
  atlas-a4-packet-biclique-decomposition: that identifies the abstract K2,2 and K2,4 packet components; this computes their field-of-definition fibers in GL4(4).
---

Embed the marked subfield chart `GL4(2)` in `GL4(4)`.  The four packet
involutions lie in one ambient conjugacy class of size `5355`.

For an ambient conjugate `x` of one packet involution, impose every adjacent
cube relation against the fixed first-chart order-three letters in one
biclique component.  The exact counts are

```text
component       ambient fan candidates       candidates over F2
H6 = S3                    336                         18
H18 = S3 x C3             150                         18.          (L44F-1)
```

Thus both one-vertex fans have nonsubfield solutions.  Even the complete
`H6` rectangle does not repair this: mapping its ordered generating
involution pair to ambient candidates, imposing both directions of all four
`K2,2` edges, leaves

```text
1262 ordered pairs, of which only 24 are defined over F2.             (L44F-2)
```

Consequently neither a single packet fan nor the complete `H6` rectangle is
a field-of-definition/support invariant for the diagonal multiplicity-two
module.  Any structural exclusion of the `L4(4)` equality case must couple
the `H6` and `H18` components through one common conjugator, or use collision
`19243` or q14.  This claim does not assert that a full-packet escape exists.

