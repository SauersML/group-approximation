---
rg: 2
id: rokhlin-supremum-torsion-products-proof
kind: route
title: Seward's vanishing theorem gives the zero side and co-amenable ascent along 1 x G gives the infinite side
target: rokhlin-supremum-of-torsion-products-is-zero-or-infinite
requires: [seward-per-group-rokhlin-entropy-of-bernoulli-shifts, rokhlin-maximality-ascends-co-amenable-subgroups, positive-rokhlin-entropy-action-gives-positive-supremum]
---

## Why sufficient

Let `G` be countably infinite and `P` countable and amenable with finite subgroups of unbounded order. Then
`P × G` is countably infinite. Write "item n" for item n of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

**Step 1: the zero side.** Suppose `h_sup(G) < ∞`. `P` contains arbitrarily large finite subgroups, so item 3
(Seward, Theorem 1.11) gives `h_sup(P × G) = 0`.

**Step 2: `G` is Rokhlin-maximal.** Suppose `h_sup(G) = ∞`. Fix `q ≥ 2`, `|A| = q`, `k ≥ 1`. The base
`L = A^k` with the uniform measure has `H(L) = k log q < ∞`. Item 1 gives
`h^Rok_G((A^k)^G) = min(k log q, ∞) = k log q`. So `G` is Rokhlin-maximal at `q` in the sense of Theorem A.

**Step 3: `1 × G` is co-amenable in the Følner sense.** Put `H = {1} × G`, which is infinite.
- For `(p, g) ∈ P × G`, the right coset is `H(p, g) = {(p, hg) : h ∈ G} = {p} × G`. So `p ↦ {p} × G` is a
  bijection `P → H\(P × G)`, and right multiplication by `s = (p_s, g_s)` sends `{p} × G` to `{p p_s} × G`.
- Let `S ⊆ P × G` be finite and `δ > 0`. `P` is amenable, so it has left Følner sets. Taking inverses turns a left
  Følner set for `{p_s^-1 : s ∈ S}` into a finite nonempty `F ⊆ P` with `|F p_s \ F| ≤ δ |F|` for every `s ∈ S`.
- Let `Ω' = {{p} × G : p ∈ F}`. Then `Ω' s = {{p p_s} × G : p ∈ F}`, so `|Ω' s \ Ω'| = |F p_s \ F| ≤ δ |Ω'|`.

This is exactly the co-amenability hypothesis of `rokhlin-maximality-ascends-co-amenable-subgroups`.

**Step 4: the infinite side.** By Steps 2 and 3, Theorem A of `rokhlin-maximality-ascends-co-amenable-subgroups`
makes `P × G` Rokhlin-maximal at `q`: `h^Rok_(P×G)((A^k)^(P×G)) = k log q` for every `k`. Item 1 for `P × G` gives
`min(k log q, h_sup(P × G)) = k log q`, so `h_sup(P × G) ≥ k log q` for every `k`. Hence `h_sup(P × G) = ∞`.

**Items 1 and 2 of the target.** Steps 1 and 4 cover both cases of `h_sup(G)`.

**Item 3 of the target.**
- POS(`P × G`) ⟹ `h_sup(P × G) > 0`, by `positive-rokhlin-entropy-action-gives-positive-supremum` (1 ⟹ 4).
- By items 1 and 2, `h_sup(P × G) > 0` ⟹ INF(`P × G`) ⟹ INF(`G`).
- INF(`G`) ⟹ INF(`P × G`), by Step 4.
- INF(`P × G`) ⟹ RBS(`P × G`).
  - Finite-entropy bases: item 1 gives `min(H(L), ∞) = H(L)`.
  - Infinite-entropy bases: item 2 applies, since `h_sup(P × G) = ∞ > 0` provides a free ergodic action of
    positive Rokhlin entropy.
- RBS(`P × G`) ⟹ POS(`P × G`). The Bernoulli 2-shift over the infinite group `P × G` is free and ergodic (it is
  mixing), and RBS gives it Rokhlin entropy `log 2 > 0`.

This closes the cycle of implications. ∎

**What each hypothesis is used for.**
- Unbounded finite subgroups of `P`: only Step 1.
- Amenability of `P`: only Step 3.
- Infiniteness of `G`: Step 3 needs `H` infinite, and item 1 needs `G` countably infinite.
