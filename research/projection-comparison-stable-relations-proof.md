---
rg: 2
id: projection-comparison-stable-relations-proof
kind: route
title: Approximate partial isometries at one stage and perturb them exactly
target: projection-comparison-lifts-through-injective-limits
requires: []
---

A projection in an inductive limit is approximated within norm less than
`1/2` by a self-adjoint element from one stage. A spectral cut at `1/2`
gives a stage projection whose limit image is unitarily equivalent to the
original projection. This proves the first assertion, after passing to a
matrix algebra and then to the stabilization.

For the second assertion, write each subequivalence `p<=q` as a partial
isometry relation

```text
v^*v=p,             vv^*<=q.
```

Approximate the finitely many implementing partial isometries by elements
from one common stage. Their finitely many relation defects tend to zero at
later stages. For one approximate implementer `x`, replace it by `qxp`. Once

```text
||p x^* q x p-p||<1,
```

the first element is invertible in `pA_ip`, and

```text
w=qxp (p x^* q x p)^(-1/2)
```

satisfies `w^*w=p` and `ww^*<=q`. Apply this correction at one stage after
all defects are below the common tolerance. Because the family is finite,
all comparisons are then exact at that same stage.

This is the direct stable-relations proof of continuity of the
Murray--von Neumann semigroup; no comparison or regularity hypothesis on the
limit is involved.
