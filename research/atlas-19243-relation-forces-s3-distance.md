---
rg: 2
id: atlas-19243-relation-forces-s3-distance
kind: claim
title: The 19243 kernel relation keeps regular atlas frames at least sqrt(2)/8 from the aligned S3 commutant
distinct_from:
  atlas-19243-centrality-forces-s3-distance: that applies to arbitrary central-extension microstates and therefore pays for the commutator of q with a chart generator; this uses the stronger hypothesis that q itself tends to one, which holds in a necessity sequence pulled back from a hypothetical hyperlinear model of Q.
artifacts:
  - experiments/atlas_19243_s3_gap.py
---

Use the notation of `atlas-19243-s3-relative-normal-form`.  Let

```text
K_19243=<r,s> ~= S3
```

and let `C_K` be the unitary commutant of its amplified regular `A8`
representation.  Let `q(U)` be collision word `19243` evaluated at relative
chart unitary `U`.  Then

```text
dist_2(U,C_K)
 >= max(0,(sqrt(2)-||q(U)-1||_2)/8).                 (19243-REL-DIST)
```

Consequently every sequence for which

```text
||q(U_n)-1||_2 -> 0
```

satisfies

```text
liminf_n dist_2(U_n,C_K) >= sqrt(2)/8,
liminf_n dist_2(U_n,C_K)^2 >= 1/32.                  (19243-REL-WALL)
```

This is four times stronger after squaring than the centrality-only wall.
It applies to the nonhyperlinearity necessity sequence: if
`Q=L_(F_2)(1,2)^x` were hyperlinear, pull its microstates back along the
two-chart map.  Since `atlas-word-19243-is-kernel-relation` gives
`q_19243 in ker(bar_rho)`, the pulled-back word has defect zero before
regularization and `o(1)` afterwards.
