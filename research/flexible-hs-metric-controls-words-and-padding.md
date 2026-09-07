---
rg: 2
id: flexible-hs-metric-controls-words-and-padding
kind: claim
title: Zero-padding HS distance controls words and has sharp upward repair cost
distinct_from:
  dv-distance-is-defect-plus-congruence-capture: that uses a cross-dimension Lipschitz step in a conditional Iwahori reduction; this proves that metric step and a sharp general conversion to upward-only comparisons without assuming congruence capture.
  sl2-half-explicit-strict-flexible-separation: that gives an arithmetic strict-repair obstruction fixed by one added dimension; this proves general metric estimates and sharpness for the class of trivial representations of C2.
artifacts:
  - research/artifacts/flexible-hs-metric-and-padding.md
---

For positive-dimensional unitaries, the zero-padding distance
`d_0(U,V)=||j_M(U)-j_M(V)||_F/sqrt(M)`, `M=max(dim U,dim V)`,
is a metric. For tuples at distance `delta`, every nonempty word of length
`ell` changes by at most `ell delta`. The uniform all-word bound uses
`max(1,ell)`, because the empty word has a nonzero dimension charge.

For any two finite lists of words of lengths at most `L>=1`, their maximum
pairwise local defect is `2L`-Lipschitz in this metric, with no ordering
restriction on the two matrix dimensions. In addition,

```text
|d-D|/max(d,D) <= d_0(U,V)^2.
```

For any nonempty class of exact representations closed under adding
trivial summands, let `A` be distance to the class over all dimensions and
`A_up` the infimum restricted to dimensions at least the input dimension.
Then `A<=A_up<=2A`. The factor two is sharp for the class of trivial
representations of C2 and inputs `diag(I_(d-k),-I_k)` with `d>4k>=4`.

This proves neither Iwahori congruence capture nor a new non-hyperlinear
group. It supplies a corrected reusable metric step in that open route.
