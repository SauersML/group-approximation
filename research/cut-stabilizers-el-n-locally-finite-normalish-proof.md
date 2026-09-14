---
rg: 2
id: cut-stabilizers-el-n-locally-finite-normalish-proof
kind: route
title: Tower algebras absorb the cut ring, and a window lemma puts locally constant matrices off a small clopen set into every conjugate
target: cut-stabilizers-of-el-n-are-locally-finite-normalish
requires: []
artifacts:
  - research/artifacts/sk-cstar-simple-2-2026-09-13-part1.md
---

Notation as in the target. `M = F_q^{(Z)} ⊗ F_q^n`, `V^J = span{δ_t : t ∈ J} ⊗ F_q^n`, and `π = π_y`.
- `π` is faithful on `M_n(R)`: the coefficients are locally constant and vanish on a dense orbit.
- The width `w(g)` is the largest `|k|` with a nonzero `u^k`-coefficient in some entry. Then `π(g)V^{≥m} ⊆ V^{≥m−w(g)}` and
  `π(g)V^{<m} ⊆ V^{<m+w(g)}`.

**Step 1 (local finiteness).**
- `g ∈ S_y` iff each entry of `g` lies in `R_y = {r : π(r)V^{<0} ⊆ V^{<0}, π(r)V^{≥0} ⊆ V^{≥0}}`, and then so does each entry of
  `g^{-1}`.
- For `r = Σ_{|k|≤w} f_ku^k`, `π(f_ku^k)δ_t = f_k(T^{t+k}y)δ_{t+k}` crosses `0` only for `t` between `−k` and `−1`. So `r ∈ R_y`
  iff `f_k(T^jy) = 0` for `j ∈ [0,k−1]` (`k>0`) and for `j ∈ [k,−1]` (`k<0`).
- Given finitely many elements of `R_y`, choose a clopen `B ∋ y` such that all their `f_k` vanish on the corresponding `T^jB`.
- By minimality, return times to `B` are bounded. Refine the Kakutani–Rokhlin partition over `B` so that every `f_k` is
  constant on every level `T^aW`.
- Let `A = span{e_{T^aW}u^{a−b} : 0 ≤ a,b < h(W)} ≅ ⊕_W M_{h(W)}(F_q)`, a finite ring. Write
  `f_ku^k = Σ_{levels} c·e_{T^aW}u^k`, where `e_{T^aW}u^k = u^ke_{T^{a−k}W}` is a matrix unit when `0 ≤ a−k < h(W)`.
- **No crossing.**
  - If `k>0` and `a<k`, the level lies in `T^aB` with `0 ≤ a ≤ k−1`, where `f_k = 0`.
  - If `k<0` and `a−k ≥ h(W)`, the level enters `B` after `j ∈ [1,|k|]` steps, so it lies in `T^{−j}B` with `−j ∈ [k,−1]`, where
    `f_k = 0`.
- So the given elements lie in `A`. Finitely many elements of `S_y` and their inverses generate a subgroup of the finite
  group `GL_n(A)`.

**Step 2 (window lemma).** Let `t ∈ G` and `W_0 ≥ max(w(t), w(t^{-1}))`. Then `π(t)V^{≥0} = W ⊕ V^{≥W_0}` and
`π(t)V^{<0} = W' ⊕ V^{<−W_0}`, with `W, W' ⊆ V^{[−W_0,W_0)}`.
- `π(t)V^{≥0} ⊆ V^{≥−W_0}`, and `V^{≥W_0} = π(t)π(t^{-1})V^{≥W_0} ⊆ π(t)V^{≥0}`.
- Split `v = v_J + v_+` with `v_+ ∈ V^{≥W_0}`. Then `v_J ∈ π(t)V^{≥0}`.
- The other half is the same.

**Step 3 (normalish).** Let `t_1,…,t_m ∈ G` and let `W_0` bound all widths of the `t_i^{±1}`.
- Let `Z` be a clopen neighbourhood of `{T^sy : −W_0 ≤ s < W_0}` with `X ∖ Z ≠ ∅`. `X ∖ Z` is infinite, since `X` has no
  isolated points.
- `K_Z = {l ∈ SL_n(LC(X,F_q)) : l ≡ I on Z}` is infinite and lies in `G`, since `SL_n(F_q) = E_n(F_q)` pointwise.
- `π(l)δ_s ⊗ e_j = Σ_i l_ij(T^sy)δ_s ⊗ e_i` acts position by position. It fixes `V^{[−W_0,W_0)}` pointwise and preserves
  `V^{≥W_0}` and `V^{<−W_0}`.
- By Step 2 it preserves `π(t_i)V^{≥0}` and `π(t_i)V^{<0}`. So `t_i^{-1}lt_i ∈ S_y`.
- Hence `K_Z ⊆ ⋂_i t_iS_yt_i^{-1}`. The case `m = 1`, `t_1 = e` shows that `S_y` is infinite.

**Modulo the centre.** `Z(G)` is finite, and the image of `K_Z` in `G/Z(G)` is infinite. ∎

**Model tests.**
- A finite orbit `X` makes `Z = X` possible, and `K_Z` is trivial, so the hypothesis "infinite" is used.
- Linear groups with trivial amenable radical have no amenable normalish subgroup (BKKO), consistent with `G_X` not being
  linear.
- The Fibonacci subshift satisfies every hypothesis.
