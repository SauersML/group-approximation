---
rg: 2
id: subshift-elementary-groups-are-not-uniformly-simple-proof
kind: route
title: Direct rank-count proof that EL_n(LC(X,F_2)⋊Z) is not uniformly simple
target: subshift-elementary-groups-are-not-uniformly-simple
requires: []
---

Direct proof. Notation as in the note (`simple_kazhdan_sofic_group.tex`, section "Finite models").
- Fix `x ∈ X`.
- `m_ℓ` is a return time of `x_[0,2ℓ)`, and `y_ℓ` is the `m_ℓ`-periodic sequence with the same words of length `2ℓ+1`
  as `X`.
- `D_ℓ(f)δ_t = f(T^t y_ℓ)δ_t` for `f` of window radius at most `ℓ`, and `φ_ℓ(Σ f_j u^j) = Σ D_ℓ(f_j)P^j` on
  `F_2^{Z/m_ℓ}`.
- `φ_ℓ` is applied entrywise to `n×n` matrices.

**Step 1: finitely many relations survive.** Suppose `h = Π_{i=1}^{M} x_i g^{ε_i} x_i^{-1}` in `G`, with `ε_i = ±1`.
Fix one such expression. It involves finitely many elements and finitely many matrix products. By the note, for all
large `ℓ`, `φ_ℓ` preserves every sum and product of entries involved. So
`φ_ℓ(h) = Π_i φ_ℓ(x_i) φ_ℓ(g)^{ε_i} φ_ℓ(x_i)^{-1}` in `GL_{n m_ℓ}(F_2)`.

**Step 2: rank is subadditive and conjugation invariant.** For `A, B ∈ GL_k(F_2)`:
- `AB − I = (A − I)B + (B − I)`, so `rank(AB − I) ≤ rank(A − I) + rank(B − I)`;
- `rank(xAx^{-1} − I) = rank(A − I)`;
- `A^{-1} − I = −A^{-1}(A − I)`, so `rank(A^{-1} − I) = rank(A − I)`.

Hence `rank(φ_ℓ(h) − I) ≤ M · rank(φ_ℓ(g) − I)`.

**Step 3: short towers give small rank.** Let `g = e_12(e_V)` with `V ≠ ∅` clopen, `V ∩ T^jV = ∅` for
`0 < |j| ≤ 2w`, and `e_V` of window radius `ρ`. Take `ℓ ≥ ρ + w` and `m_ℓ > 2w`.

`φ_ℓ(g) − I` is `D_ℓ(e_V)` in block `(1,2)`, so its rank is the number of `t ∈ Z/m_ℓ` with `e_V(T^t y_ℓ) = 1`.
Suppose `t` and `t + j` both count, with `0 < |j| ≤ 2w` (indices mod `m_ℓ`).
- The window of `y_ℓ` covering `[t − ρ, t + j + ρ]` has length at most `2ρ + 2w + 1 ≤ 2ℓ + 1`.
- So it is a word of `X`: some `z ∈ X` agrees with `T^t y_ℓ` on the coordinates `[−ρ, j + ρ]`.
- Then `z ∈ V` and `T^j z ∈ V`, so `V ∩ T^{-j}V ≠ ∅`.

That contradicts the choice of `V`. So the counted positions are pairwise at cyclic distance at least `2w+1`, and
there are at most `m_ℓ/(2w+1)` of them.

**Step 4: the count.** `φ_ℓ(e_12(1)) − I` has the block `I_{m_ℓ}` in position `(1,2)`, so its rank is `m_ℓ`. If
`e_12(1)` is a product of `M` conjugates of `e_12(e_V)^{±1}`, Steps 1–3 give `m_ℓ ≤ M · m_ℓ/(2w+1)` for large `ℓ`.
So `M ≥ 2w + 1`.

**Step 5: existence of V, and conclusion.**
- An infinite minimal subshift has no periodic points.
- So every point has a clopen neighbourhood `V` with `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`, for each `w`.
- Then `g_w = e_12(e_V) ≠ 1`, and `e_12(1)` needs at least `2w+1` conjugates of `g_w^{±1}`.
- Since `w` is arbitrary, no uniform bound exists.

The group `G` is simple (the note), so each `e_12(1)` is some finite product of such conjugates. Only the bound fails.

**Model tests.**
- `SL_3(F_2)` (finite, `X` a single fixed point): no `V` with no returns exists, and a finite simple group is
  uniformly simple. The hypothesis correctly fails there.
- Fibonacci subshift: `V` = a long cylinder has no returns up to about its length, so the bound grows linearly. It
  agrees with the Sturmian rank count in `sturmian-elementary-group-lef-growth-is-exp-r-squared`.
