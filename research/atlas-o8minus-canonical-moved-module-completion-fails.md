---
rg: 2
id: atlas-o8minus-canonical-moved-module-completion-fails
kind: claim
title: The canonical Omega8-(2) singular-parabolic overgroup cannot complete either marked Q1920 seam
artifacts:
  - experiments/atlas_a4_q1920_o8m_discovery.g
  - research/artifacts/atlas-a4-q1920-o8minus-seam.json
distinct_from:
  atlas-o8plus-canonical-moved-module-completion-fails: that excludes the plus-type orthogonal host with Levi A8; this excludes the minus-type host with Levi U4(2).
  atlas-sp6-canonical-moved-module-completion-fails: that excludes the lower-rank symplectic parabolic with radical order32; this handles the minus-type radical of order64.
---

The singular-vector stabilizer in `Omega8-(2)` has order 1658880, elementary
abelian 2-core of order 64, and Levi factor `U4(2)` of order 25920.  Its two
classes of `A5` subgroups have respectively one and three invariant
order-32 radical submodules; exactly the unique submodule in the first class
has the required Q1920 orbit/span profile.

This gives one parabolic conjugacy class of `Q=2^5:A5`.  As in the plus-type
case, its ambient normalizer has order 7680 and induces an order-3840
subgroup of `Aut(Q)`, leaving exactly two embedding twists.  For either
marked tuple the exact profiles are

```text
(|C(A)|, collision count, seam count)=(8,0,0),(120,0,0).  (O8M-1)
```

Thus the canonical `Omega8-(2)` moved-module host contains no faithful
marked collision involution.  Together with the Sp6(2) and Omega8+(2)
calculations, this exhausts the immediate rank-three/rank-four classical
parabolic hosts suggested by the five-dimensional module; it is not a CFSG
classification of arbitrary completions.
