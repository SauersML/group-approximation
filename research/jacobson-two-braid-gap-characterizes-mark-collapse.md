---
rg: 2
id: jacobson-two-braid-gap-characterizes-mark-collapse
kind: claim
title: One exact-packet two-braid infimum characterizes Jacobson joint mark collapse
artifacts:
  - research/artifacts/jacobson-two-braid-reduction-2026-09-07.md
distinct_from:
  mf-radical-words-have-linear-certificates: that treats arbitrary finite word data; this uses the concrete finite Jacobson packet to leave only two braid errors, with all packet, overlap and involution relations exactified in the original matrix dimension.
---

For the group and mark in `jacobson-joint-cells-are-two-braids`, let
`gamma` be the infimum of

```
max(||(H pi(b))^3-I||, ||(H pi(d_P))^3-I||)
```

over all dimensions, exact representations `pi:F->U(d)` retaining the
mark, and self-adjoint unitary `H` commuting with `pi(K)`.
Then `0<=gamma<2`, and `gamma>0` if and only if every norm-corona
homomorphism from this joint group kills the mark.

The theorem does not assert positivity. Its proof exactifies a finite
group representation by a regular dilation and spectral cut, then
averages the involution over the finite overlap. Both corrections keep
the original dimension and use no Property-(T) input.

The strict upper bound uses the explicit mixed packet in
`jacobson-mixed-packet-attains-rank-eight-below-two`.
