---
rg: 2
id: leavitt-d4-l12-rank10-fifteen-cyclic-proof
kind: route
title: Enumerate the cyclic rank-ten signatures without assuming a false inversion pairing
target: leavitt-d4-l12-rank10-fifteen-cyclic-classes
requires:
  - leavitt-d4-length12-balanced-rank9-is-fenced
---

Run

```text
python3 research/artifacts/rank-degree4-length12-triangles.py \
  --profile=---+-+++++++ --balanced-only --classify-rank=10
```

The fixed profile has 201 exact rank-ten embeddings, 99 normal and 102
inverse.  Forgetting the cyclic rotation of each target face and cyclically
choosing any of the three five-face arcs first gives the following canonical
`(start;sizes)` keys:

```text
normal:  0;113  0;122  0;131  0;212  0;311  1;113  2;113
inverse: 0;113  0;122  0;131  0;212  0;311  1;113  1;212  2;113
```

Thus there are exactly fifteen classes under the stated cyclic quotient.
The unequal chirality counts prove that global inversion is not closed on the
stored representative: applying it requires the accompanying ambient slot
reversal/rotation.  No global-inversion identification is used in this claim.
