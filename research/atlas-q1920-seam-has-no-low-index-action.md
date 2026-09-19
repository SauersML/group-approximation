---
rg: 2
id: atlas-q1920-seam-has-no-low-index-action
kind: claim
title: Neither marked order-1920 rectangle colimit has a faithful transitive action through degree twelve
artifacts:
  - experiments/atlas_a4_non_a5_fj_colimits.g
  - research/artifacts/atlas-a4-q1920-fj-low-index.json
distinct_from:
  atlas-q168-rectangles-collapse-fj-seam: that is an unbounded exact colimit collapse for all six marked order-168 classes; this is only a complete degree-at-most-twelve action census for the two order-1920 classes.
  atlas-a5-large-rectangle-cannot-share-marked-collision-seam: that gives a symbolic transported-intersection contradiction for the A5 local completion; the order-1920 radial S3 subgroups have trivial intersection.
---

The degree-at-most-twelve local rectangle census has exactly two faithful
marked images of order 1920.  For each one, freeze its complete marked
multiplication table and adjoin the same first-packet and collision seam
relations used in the order-168 colimit calculation.  Enumerating every
subgroup of index at most twelve in each exact finitely presented colimit
gives the identical action histogram recorded in the artifact.

No action simultaneously has

```text
|image(Q)|=1920,       |image(F)|=36,       |image(J)|=24.    (Q1920-LI-1)
```

The only degree-ten action retaining collision `J=S4` instead has
`|image(Q)|=60` and `|image(F)|=12`.  Conversely, both degree-twelve actions
retaining the full local `Q` collapse `z=c=1`, so `F` and `J` both have order
six.  Thus neither marked Q1920 seam has a faithful common-frame carrier of
permutation degree at most twelve.

This is deliberately a bounded statement.  Exact relative coset
enumeration already exceeded GAP's 4,096,000-coset ceiling, and no conclusion
about the order, infinitude, residual finiteness, or higher-degree finite
quotients of either universal colimit follows from that overflow.
