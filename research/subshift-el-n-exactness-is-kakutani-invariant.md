---
rg: 2
id: subshift-el-n-exactness-is-kakutani-invariant
kind: claim
title: Exactness of every EL_n over a minimal subshift crossed product is invariant under Kakutani equivalence, and EL_3 over the k-tower system is EL_3k over the base
distinct_from:
  subshift-elementary-groups-are-exact: that is the open exactness question for G_X; this proves transfer lemmas between ranks and between Kakutani-equivalent systems
  cyclic-factor-subshift-el-2-is-simple-kazhdan-lef: that uses a clopen cyclic tower to write R_X as M_m over a corner and prove simplicity in rank two; this uses corners and towers to move exactness across ranks and induced systems
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- For a minimal Cantor system `(X,T)` put `R_X = LC(X,F_2) ⋊_T Z`. The proof works over any finite field.
- For a nonempty clopen `V ⊆ X`, `X_V` denotes the induced system `(V,T_V)`.
- For `k ≥ 1`, the `k`-tower system `X^{(k)} = X × {0,…,k−1}` has `T′(x,i) = (x,i+1)` for `i < k−1` and `T′(x,k−1) = (Tx,0)`.
- `X` and `Y` are Kakutani equivalent if they have conjugate induced systems on nonempty clopen sets.

**Theorem.**
- **(a)** For every unital ring `S` and `n ≥ 2`, `EL_n(M_k(S)) = EL_{nk}(S)`.
- **(b)** `R_{X^{(k)}} ≅ M_k(R_X)`, so `EL_3(R_{X^{(k)}}) ≅ EL_{3k}(R_X)`. If `X` is an infinite minimal subshift, so is `X^{(k)}`.
- **(c)** For every nonempty clopen `V ⊆ X` there is `k ≥ 1` with `EL_n(R_{X_V}) ≤ EL_n(R_X) ≤ EL_{nk}(R_{X_V})` for all `n ≥ 2`.
- **(d)** Consequently:
  - `{n ≥ 3 : EL_n(R_X) is exact}` is an initial segment of `{3,4,…}`;
  - if `X` and `Y` are Kakutani equivalent, `EL_n(R_X)` is exact for all `n` iff `EL_n(R_Y)` is exact for all `n`;
  - `G_X` is exact for every infinite minimal subshift `X` iff `EL_n(R_X)` is exact for every `n ≥ 3` and every such `X`.

**Proof:** `subshift-el-n-exactness-kakutani-invariance-proof`.
