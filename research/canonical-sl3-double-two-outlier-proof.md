---
rg: 2
id: canonical-sl3-double-two-outlier-proof
kind: route
title: Take the contrapositive of the one-vertex anchor and projective fold estimates
target: canonical-sl3-double-microstates-are-uniform-two-vertex-outliers
requires:
  - sl3-double-one-near-vertex-forces-joint-near-exactness
  - sl3-arithmetic-double-near-exact-vertices-fold-projectively
---

Let `dist_j(sigma)` be the infimum, over exact `d`-dimensional
representations of `A`, of the maximum normalized-HS distance on the fixed
vertex generators.  The first prerequisite has a dimension-free modulus:
small presentation defect and small `dist_j` make the other vertex close to
the same exact representation.  The second prerequisite has a
dimension-free modulus: two such near-exact vertices force the fold
coefficient `|tr(sigma(w))|` to tend to one.

Choose fixed input thresholds small enough that the composite modulus gives

```text
dist_j(sigma)<epsilon_0 and defect(sigma)<delta_0
    => |tr(sigma(w))|>3/4.
```

The argument is symmetric in the two vertices.  Therefore an assignment
with defect below `delta_0` and fold trace modulus at most `1/4` has
`dist_j(sigma)>=epsilon_0` for `j=0,1`.  Canonical-character microstates have
defect tending to zero and, because `w!=1` by amalgam normal form, fold trace
tending to zero.  This proves the target.
