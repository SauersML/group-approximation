---
rg: 2
id: thompson-t-disjoint-pair-cstar-simple-subgroup-criterion-proof
kind: route
title: The disjoint-pair element dies in the dyadic quasi-regular representation of T, which factors through C*_r(T) when F is amenable
target: thompson-t-disjoint-pair-cstar-simple-subgroup-criterion
requires: []
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md
---

Full proof: `research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md`,
§2, Theorem D.

1. `1, a, b, ab` are pairwise distinct, because `a, b ≠ 1` and their supports are disjoint and
   nonempty. So `x = 1 − λ(a) − λ(b) + λ(ab) ≠ 0` in `C[H] ⊆ C*_r(H)`.
2. Let `π` be the quasi-regular representation of `T` on `l^2(T·0)`, so `Stab_T(0) = F`. For
   each `q`, `π(x)δ_q = δ_q − δ_(aq) − δ_(bq) + δ_(abq)`.
   - If `aq = q`, then `abq = bq`, since `a` fixes `supp(b)` pointwise.
   - If `aq ≠ q`, then `bq = q`.

   Either way the sum is `0`, so `π(x) = 0`.
3. Suppose `F` is amenable. Then `1_F ≺ λ_F`, so `π = Ind_F^T 1_F ≺ Ind_F^T λ_F = λ_T` by Fell
   continuity of induction. Hence `π` extends to a unital *-representation of `C*_r(T)`.
4. `C*_r(H)` embeds unitally and isometrically in `C*_r(T)`, since `λ_T|_H` is a multiple of
   `λ_H`. The restriction of the extension of `π` is a unital representation of `C*_r(H)` that
   kills `x`.
5. A unital representation of a simple unital C*-algebra is injective, and `x ≠ 0`. This
   contradicts step 4, so `F` is not amenable.
