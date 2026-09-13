---
rg: 2
id: virtually-free-by-cyclic-no-bs-one-n-proof
kind: route
title: Kill BS(1,n) inside free-by-cyclic groups with its abelianization and its abelian subgroup Z[1/n]
target: virtually-free-by-cyclic-groups-contain-no-bs-one-n
requires: []
---

Let `H ≅ F_k ⋊ Z` have finite index in `G`, let `π : H -> Z` be the quotient map
with kernel `F_k`, and suppose `B <= G` is isomorphic to `BS(1,n)` with `|n| >= 2`.
Model `B` as `Z[1/n] ⋊ <c>`, with `b = 1 ∈ Z[1/n]` and `c^-1 t c = n t`.

1. **Pass into `H`.** `B ∩ H` has finite index in `B`, so it contains `b^j` and
   `c^m` for some `j, m >= 1`. Then `(c^m)^-1 b^j c^m = (b^j)^(n^m)`. The subgroup
   `<b^j, c^m>` is `j Z[1/n] ⋊ <c^m>`, and `t ↦ t/j`, `c^m ↦ c` identifies it with
   `Z[1/n^m] ⋊ Z = BS(1, n^m)`, since `Z[1/n^m] = Z[1/n]`. Replacing `n` by `n^m`,
   we may assume `B <= H` and still `|n| >= 2`.
2. **The subgroup `A`.** The normal closure of `b` in `B` is `A = Z[1/n]`. It is
   abelian and not cyclic, because it is not finitely generated when `|n| >= 2`.
   Every abelian subgroup of a free group is cyclic, so `A` lies in no free group.
3. **Case `π(B) = 0`.** Then `B <= F_k`, so `A <= F_k`, contradicting step 2.
4. **Case `π(B) ≠ 0`.** The restriction `π|_B : B -> Z` factors through
   `B^ab`. The relation `c^-1 b c = b^n` gives `(n-1) b = 0` in `B^ab`, so `b` has
   finite order there and maps to `0 ∈ Z`. Hence `A <= ker π ∩ B <= F_k`, again
   contradicting step 2. `∎`
