---
rg: 2
id: full-defect-in-m-by-m-kills-mf-quotients-of-el-2m-proof
kind: route
title: Apply the rank-two full-defect theorem to M_m(R), identify EL_2(M_m(R)) with EL_2m(R), and spread along conjugate root subgroups
target: full-defect-in-m-by-m-kills-mf-quotients-of-el-2m
requires: [full-defect-ring-non-mf-at-rank-two]
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

1. **Rank two over the amplified ring.** `M_m(R)` is a countable unital ring with `ts = 1` and
   `M_m(R)(1−st)M_m(R) = M_m(R)`. By `full-defect-ring-non-mf-at-rank-two` (printed Theorem [full
   complementary idempotents], l.918, `n >= 2`), every homomorphism from `EL_2(M_m(R))` to an MF group is
   trivial.
2. **Block identification (artifact Lemma 1).** Under `M_2(M_m(R)) = M_(2m)(R)`:
   - a block generator `e_12(A)` is the commuting product `∏_(a,b) e_((1,a),(2,b))(A_ab)`, so it lies in `EL_(2m)(R)`;
   - a cross-block generator of `EL_(2m)(R)` is a block generator `e_12(rE_ab)` or `e_21(rE_ab)`;
   - a same-block generator is `e_((i,a),(i,b))(r) = [e_((i,a),(k,1))(r), e_((k,1),(i,b))(1)]` with `k ≠ i`,
     by the Steinberg relation `[e_pq(x), e_qs(y)] = e_ps(xy)`, for distinct `p, q, s`.

   So `EL_2(M_m(R)) = EL_(2m)(R)`, and every homomorphism from `EL_(2m)(R)` to an MF group is trivial.
3. **Spreading (artifact Lemma 2).** Let `N >= 2m` and `φ : EL_N(R) → M` with `M` MF.
   - The first `2m` coordinates carry a subgroup copy of `EL_(2m)(R)`, so `φ(X_12) = 1`.
   - For `p ≠ q`, `w_pq = e_pq(1)e_qp(−1)e_pq(1)` acts as `[[0,1],[−1,0]]` on coordinates `p, q`, so
     `w_pq e_kl(r) w_pq^-1 = e_(τk,τl)(±r)` with `τ = (p q)`.
   - `S_N` is transitive on ordered pairs, so every root subgroup `X_ij` is conjugate to `X_12`, and `φ(X_ij) = 1`.
   - The `X_ij` generate `EL_N(R)`, so `φ` is trivial.
