---
rg: 2
id: unit-corner-embedding-normally-generates-commutators
kind: claim
title: The corner copy of the rank-four elementary group normally generates the whole commutator subgroup of the units
distinct_from:
  elementary-rank-descent-to-two: that normally generates the rank-two elementary group over any ring with a properly infinite unit; this normally generates the commutator subgroup of the full unit group, and uses pure infiniteness and simplicity.
  properly-infinite-unit-rank-two-normal-generator: that names one generator of EL_2; this identifies the normal closure of a whole embedded rank-four elementary group inside the unit group.
  agp-purely-infinite-simple-k1-is-unit-abelianization: that identifies the quotient of the unit group by its commutator subgroup; this identifies that commutator subgroup as one normal closure.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

Let `R` be a countable unital purely infinite simple ring.  Choose four
mutually orthogonal copies of `R_R` inside `R_R` with nonzero complementary
summand, with insertion and extraction maps `T_iS_j = delta_(ij)` and
`p = sum_i S_iT_i != 1`, and let

```text
jmath(A) = 1 - p + sum_(i,j) S_i A_(ij) T_j
```

be the resulting embedding `GL_4(R) -> R^x`.  Then

```text
<< jmath(EL_4(R)) >>_(R^x) = [R^x, R^x].
```

The point is normal generation of the whole commutator subgroup, not merely
the presence of an embedded copy.
