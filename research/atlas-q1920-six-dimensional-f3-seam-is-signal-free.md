---
rg: 2
id: atlas-q1920-six-dimensional-f3-seam-is-signal-free
kind: claim
title: The faithful six-dimensional F3 Q1920 packets admit no collision involution carrying z
artifacts:
  - experiments/atlas_a4_q1920_f3_dim6_seam_search.g
  - research/artifacts/atlas-a4-q1920-f3-dim6-seam.json
distinct_from:
  atlas-no-perfect-solvable-a5-action-on-f3-four-space: that closes four-dimensional chief factors by classifying their full action images; this directly solves the collision equations on the faithful six-dimensional local modules.
---

For each marked `Q1920` class there is one faithful irreducible
six-dimensional `F3[Q]` module with nonzero fixed space for the first radial
`A=S3`.  Its exact `A`-centralizer in `GL6(3)` has order 3888 and contains 110
elements of order dividing two.

Exhausting those elements gives the common profile

```text
triangle solutions to (c t)^3=1:                     1,
solutions also satisfying collision q19243:          1,
nonidentity collision solutions:                     0.   (Q1920-F3D6-1)
```

Thus the identity is the only `A`-central involution satisfying the triangle
and collision relations.  Its minus-one eigenspace is zero, so it cannot
invert a nonzero `A`-fixed vector representing `z`.  The six-dimensional
chief-factor escape is impossible for both markings.

## Attempts

Direct enumeration is exact and small in dimension six.  It does not scale to
dimension ten, whose `A`-centralizer has order `2^6*3^14`; those modules require
the idempotent polynomial equations in the nineteen-dimensional algebra
`End_A(E)` rather than element enumeration.
