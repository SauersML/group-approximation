---
rg: 2
id: purely-infinite-simple-algebras-have-nonsofic-el-groups-proof
kind: route
title: The neutral element of the cancellative projective group is a halvable corner
target: purely-infinite-simple-algebras-have-nonsofic-el-groups
requires: [agp-purely-infinite-simple-rings-have-cancellative-projectives, halvable-corner-makes-elementary-groups-nonsofic]
---

1. **The neutral class.** By `agp-purely-infinite-simple-rings-have-cancellative-projectives`,
   the monoid `V(R)*` of isomorphism classes of nonzero finitely generated projective right
   `R`-modules is a group under direct sum. Let `epsilon = [P]` be its neutral element, so `P != 0`.
2. **P is a corner.** `[R] ∈ V(R)*`, so `epsilon + [R] = [R]`, that is, `P ⊕ R ≅ R`. Then `P` is
   isomorphic to a direct summand of `R_R`, so `P ≅ eR` for an idempotent `e ∈ R`, with `e != 0`.
3. **P is halvable.** `epsilon + epsilon = epsilon` gives `eR ⊕ eR ≅ eR`.
4. **Conclusion.** Apply `halvable-corner-makes-elementary-groups-nonsofic` with `d = 1`. QED
