---
rg: 2
id: purely-infinite-simple-projective-elementary-groups-proof
kind: route
title: The neutral projective class gives a halvable corner, the corner lemma kills soficity of the quotient, and simplicity turns nonsoficity into stability
target: purely-infinite-simple-projective-el-groups-stable-nonsofic
requires: [agp-purely-infinite-simple-rings-have-cancellative-projectives, halvable-corner-makes-projective-elementary-groups-nonsofic, infinite-simple-group-permutation-stable-iff-nonsofic]
---

1. **A halvable idempotent.** By `agp-purely-infinite-simple-rings-have-cancellative-projectives`, `V(R)*` is
   a group. Its neutral element is `[eR]` for a nonzero idempotent `e ∈ R`, with `eR ⊕ eR ≅ eR`. This is steps
   1–3 of `purely-infinite-simple-algebras-have-nonsofic-el-groups-proof`.
2. **Nonsofic.** Apply `halvable-corner-makes-projective-elementary-groups-nonsofic` with `d = 1`, `n = N >= 2` and
   `C = Z ⊆ k^x · 1`. So `S_N = EL_N(R)/Z` is nonsofic.
3. **Infinite.** A countable purely infinite simple ring is not a division ring, and a finite simple ring is some
   `M_m(F_q)`, which has no infinite idempotents. So `R` is infinite, and `EL_N(R)` contains the infinite group
   `{1 + r E_12}`. That subgroup meets the scalars only in `1`, so `S_N` is infinite.
4. **Stable.** If `S_N` is simple, it is an infinite simple nonsofic group, so by
   `infinite-simple-group-permutation-stable-iff-nonsofic` it is strictly and flexibly permutation stable with
   trivial correcting homomorphisms. An infinite simple group has no nontrivial finite quotient, so it is not
   residually finite. QED
