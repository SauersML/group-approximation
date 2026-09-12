---
rg: 2
id: atlas-square-root-collision-constant-term-is-zero
kind: claim
title: The square-root collision polynomial has zero constant term
artifacts:
  - experiments/atlas-word-19243.json
  - experiments/atlas_a4_19243_component_localization.py
distinct_from:
  atlas-a4-19243-classical-collapse: that excludes alignments satisfying the packet and collision simultaneously; this evaluates collision alone at the literal identity frame, which is not a packet alignment.
  atlas-19243-s3-relative-normal-form: that absorbs a fixed packet reference alignment before writing the S3 equation; this works before that alignment and computes the actual constant term of the two-matrix polynomial.
---

ESTABLISHED.  For the two-matrix chart

```text
That(X,Y)=I+E13 tensor X+E14 tensor Y,
```

the collision residual polynomial satisfies

```text
P_collision(0,0)=0.                                  (SCC1)
```

Indeed, the four second-chart syllables of collision `19243` generate the
named `S3` factor `K` and have product one.  The repeated first-chart
syllable is an involution `b` centralizing every element of `K`.  Therefore
at the identity relative frame the interleaved word rearranges as

```text
(product of the four K letters) b^4=1.               (SCC2)
```

This invalidates any collision density argument based on a nonzero constant
term.  In particular collision-small does not by itself force
`rank[X Y]>=s/8`.  The classical-collapse theorem remains consistent:
identity is collision-zero but is not among the alignments satisfying the
whole packet.
