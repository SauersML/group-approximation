---
rg: 2
id: negative-base-pisot-stein-groups-are-contracting-rsgs-proof
kind: route
title: The negative-base map has Z[β] as its boundary set, and the positive-base finite-nucleus argument goes through with slopes ±β^k
target: negative-base-pisot-stein-groups-are-contracting-rsgs
requires: [contracting-rsgs-embed-in-fp-simple-groups, pisot-stein-groups-are-contracting-rsgs]
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

Notation: `D := ⌈β⌉`; `σ` ranges over the non-identity embeddings, and `ρ_σ = |σβ| < 1`.

1. **Coding.**
   - **Branches.** The inverse branches of `T'` are `x ↦ (k − x)/β = k/β + (−β)^{−1}x`. So a level-`n` cylinder is
     `I_w = a_w + (−β)^{−n} I_{t(w)}`, with `a_w ∈ Z[β]`, where `I_v` are the follower intervals. Their orientation
     alternates with `n`.
   - **Follower intervals.** Their endpoints lie in `E := {0, 1} ∪ {T'^n(D − β) : n ≥ 0}`. The last branch
     `((D−1)/β, 1)` maps onto `(D−β, 1)`, and one-sided limits of `T'` at points of `E` stay in `E`, since at a branch
     point they are `0` and `1`. The orbit of `D − β` lies in `Z[β]` and reaches `0` by (F−₀), so `E` is finite, there
     are at most `|E|²` follower intervals, and `Γ` is finite and deterministic.
   - **Strong connectivity.** `v_0` reaches every vertex by definition. Conversely, a subinterval `J` that contains
     no full branch `((k−1)/β, k/β]` meets at most two branches, and the image of the larger part has length
     `≥ (β/2)|J|`. Since `β > 2`, lengths grow until some descendant contains a full branch, whose image is
     `[0,1)`. So every vertex reaches `v_0`.
   - **Boundary set.** Put `λ(z) := min{n : T'^n z = 0}`, finite for `z ∈ Z[β] ∩ [0,1)` by (F−₀).
     - If `λ(z) ≤ n`, then `z` is an endpoint of its level-`n` cylinder, since `0` is the left endpoint of `I_{v_0}`.
     - Conversely, the level-`n` endpoints are `a_w + (−β)^{−n}b` with `b ∈ E`. Let `m_0` bound `λ` on `E ∖ {1}`.
       Following one-sided limits, such an endpoint has `λ ≤ n + m_0 + 1`: if a limit reaches `1`, the previous
       point was a branch point, which `T'` sends to `0`.
     - So the boundary set is exactly `Z[β] ∩ [0,1)`. `π` is a homeomorphism from `C_{v_0}` onto the Cantorized
       interval, and elements of `G^±_β` act as homeomorphisms (Tanner's realization, with flips allowed).
   - **Thompson group.** Canonical similarities `C_α → C_{α'}` with `t(α) = t(α')` are
     `y ↦ a_{α'} + (−β)^{|α|−|α'|}(y − a_α)`, which lie in `G^±_β`. So `V_{Γ,C_{v_0}} ≤ G^±_β`.
2. **Length lemma.** For every `C` there is `L(C)` with the following property. If `z ∈ Z[β] ∩ [0,1)` and
   `|σz| ≤ Cρ_σ^{−n}` for all `σ`, then `λ(z) ≤ n + L(C)`.
   - `T'^n z = (−β)^n z + Σ_{i≤n} k_i(−β)^{n−i}`, so `|σ(T'^n z)| ≤ C + D/(1−ρ_σ)`.
   - That puts `T'^n z` in the finite set of points of `Z[β] ∩ [0,1)` with those conjugate bounds.
   - `L(C)` is the maximum of `λ` over that set, finite by (F−₀).
   - Also: `λ(b) ≤ L` implies `|σb| ≤ (D/(1−ρ_σ))ρ_σ^{−L}`.
3. **Slope defect and offsets.** Take `f ∈ G^±_β`, a deep cone `w` inside one piece `y ↦ sβ^k y + c`, and
   `J = f(I_w)`.
   - **Defect.** Suppose a cylinder endpoint `b` of level `L ≥ L_0(c)` lies in the interior of `J`. Then
     `p = f^{−1}(b)` is interior to `I_w`, so `λ(p) > |w|`. Since `λ(b) ≤ L + m_0 + 1`, step 2 gives
     `|σp| ≤ C_β ρ_σ^{−(k+L)}` (for `L ≥ L_0(c)`, the term `σc` is absorbed), and then `λ(p) ≤ k + L + L_β`. Hence
     `L > |w| − k − L_β`.
     - Coarse endpoints, with `L < L_0(c)`, are finitely many and are absorbed into `N(f)`, exactly as in step 3 of
       `pisot-stein-groups-are-contracting-rsgs-proof`.
     - So `J` lies in one cylinder of level `|w| − k − L_β`. Also `|J| = β^k|I_w|`, and follower intervals have
       length bounded below. So the deepest cylinder `ō` containing `J` has level within a bounded window around
       `|w| − k`, and the slope exponent `e = |ō| + k − |w|` of the local action lies in a window independent of `f`.
   - **Offsets.** The local action is `x ↦ d + s'β^e x`, with `s' = ±1` and
     `d = (−β)^{|ō|}(sβ^k a_w + c − a_ō) ∈ Z[β]`. Its conjugates are bounded as in step 4 of that proof, so `d` lies
     in a finite set independent of `f`.
   - **Finite nucleus.** Deep local actions are determined by `(t(w), t(ō), s', e, d)`, a finite set. So `G^±_β`
     is rational with finite nucleus.
4. **Conclusion.**
   - `Γ` is irreducible and `G^±_β ⊇ V_{Γ,C_{v_0}}`, so `G^±_β` is a contracting RSG.
   - It is full: a homeomorphism that locally agrees with `G^±_β` is a finite patchwork of such pieces, with
     clopen pieces having endpoints in `Z[β]`. So BBMZ Theorem A (`contracting-rsgs-embed-in-fp-simple-groups`,
     item 4) gives finite presentation, and item 5 gives the embedding. ∎
