---
rg: 2
id: unit-abelianization-to-algebraic-k1-not-injective
kind: claim
title: The unit-group abelianization can fail to inject into algebraic K1
distinct_from:
  agp-purely-infinite-simple-k1-is-unit-abelianization: that is the positive theorem for purely infinite simple rings, where the two groups agree; this is the counterexample showing that conclusion uses pure infiniteness and fails for a simple stably finite algebra.
  simple-ah-witness-is-elementary-in-rank-two: that is the vanishing of one class in algebraic K_1; this is the failure of injectivity, which needs in addition that the class survives in the abelianization.
  topological-k1-cannot-detect-integral-whitehead: that is about a vanishing corona invariant detecting nothing; this exhibits a specific nonzero element of a unit-group abelianization dying in algebraic K_1 of the same algebra.
artifacts:
  - research/artifacts/ah-k1-mf-bridge-2026-09-07.md
---

Let `A` be the simple unital nuclear stably finite AH algebra of
`stw59-simple-ah-non-k1-injective` and `v` its witness.  Then the natural map

```text
(A^x)^ab --> K_1^alg(A)
```

is **not** injective: the class of `v` is nonzero on the left and zero on the
right.

The contrast is sharp against
`agp-purely-infinite-simple-k1-is-unit-abelianization`, where for a purely
infinite simple ring the two groups coincide.  So the identification of the
unit-group abelianization with algebraic `K_1` genuinely uses pure
infiniteness, and a simple stably finite algebra can carry abelian unit-group
information that stabilization destroys.

The surviving information here is detected by the finite group `Z/2`.
No claim is made that `K_1^alg(A)` vanishes; this identifies one nonzero
element of the abelianization in its kernel.
