---
rg: 2
id: full-defect-in-m-by-m-kills-mf-quotients-of-el-2m
kind: claim
title: A full complementary idempotent in M_m(R) kills every MF quotient of EL_N(R) for every N >= 2m
distinct_from:
  full-defect-ring-non-mf-at-rank-two: that is the case m = 1, a full defect in R itself, from rank two; this moves the defect to any matrix amplification M_m(R), at the price of rank 2m
  full-complementary-idempotent-elementary-full-mf-radical: that is the rank-four criterion for a full defect in R itself; this is the matrix-amplified form, from rank 2m
  stably-infinite-ring-elementary-groups-have-no-mf-quotient: that takes a paradoxical multiple 2n[1] <= n[1] of the unit and gives rank 2n (un-paradox, landed first); this takes an explicit full defect idempotent in M_m(R) and gives rank 2m, the matrix level of the defect, which is at most the paradox level and equals it for simple rings
  paradoxical-ring-el-n-full-mf-radical-from-twice-level: that is the same rank-2n conclusion from (n+1)[R] <= n[R] (un-middle); a paradox at level n yields a full defect in M_n(R), so that statement is the case m = n of this one
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

**ESTABLISHED** (route `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m-proof`; artifact §§1–2). Unreviewed.

Let `R` be a countable unital ring and `m >= 1`. Suppose `s, t ∈ M_m(R)` satisfy

```text
ts = 1,        M_m(R) (1 − st) M_m(R) = M_m(R).
```

Then for every `N >= 2m`, every homomorphism from `EL_N(R)` to an MF group is trivial.

Two ingredients, proved in the artifact:
- **Block identification.** `EL_n(M_m(R)) = EL_(nm)(R)` inside `GL_(nm)(R)` for `n >= 2`. Same-block
  generators are commutators `[e_((i,a),(k,1))(r), e_((k,1),(i,b))(1)]` of cross-block ones.
- **Conjugate root subgroups.** In `EL_N(R)`, `N >= 2`, the Weyl elements `e_pq(1)e_qp(−1)e_pq(1)` conjugate
  each root subgroup `X_ij` onto `X_12`.

With `m = 1` this is `full-defect-ring-non-mf-at-rank-two`.

**Overlap and credit.** The same stabilization was found independently and at the same time by `un-paradox`
(`stably-infinite-ring-elementary-groups-have-no-mf-quotient`, landed first) and `un-middle`
(`paradoxical-ring-el-n-full-mf-radical-from-twice-level`). Those nodes phrase the hypothesis as a paradox in
`V(R)`.
- A paradox at level `n` gives a full defect in `M_n(R)`, so those statements are the case `m = n` here.
- A full defect `1 = Σ_(j<=k) a_j e b_j` in `M_m(R)` gives `(km+m)[1] <= km[1]`, a paradox at a level at most
  `km`. So the rank bound `2m` here can be smaller when `k > 1`.
- For simple rings the two levels coincide.
