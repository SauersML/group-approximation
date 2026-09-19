---
rg: 2
id: thompson-v-elements-need-unboundedly-many-non-f-letters
kind: claim
title: "Words for elements of Thompson's group V need unboundedly many letters outside F: the order-break count is subadditive"
invalidates:
  - thompson-v-quadratic-via-bounded-non-f-normal-form
---

**Established (elementary; proof in
`thompson-v-elements-need-unboundedly-many-non-f-letters-proof`).**

Let V act on the Cantor set `C = {0,1}^N` by prefix replacement, and order `C`
lexicographically. An *interval* is a clopen order-convex subset of `C`. For
`g ∈ V` let `br(g)` be the least `k` such that `C` is a disjoint union of `k`
intervals `I_1, …, I_k` with `g` order-preserving on each `I_j` and each
`g(I_j)` an interval.

1. `br(f) = 1` for `f ∈ F`, and `br(g^(-1)) = br(g)`.
2. `br(gh) ≤ br(g) + br(h) − 1` for all `g, h ∈ V`. So for any word
   `s_1 ⋯ s_L` of elements of V,
   `br(s_1 ⋯ s_L) ≤ 1 + Σ_i (br(s_i) − 1)`, and letters from F contribute 0.
3. For `k ≥ 0` let `r_k ∈ V` reverse the `2^k` cones of depth `k`:
   `r_k(w_i ζ) = w_(2^k + 1 − i) ζ`, where `w_1 < ⋯ < w_(2^k)` are the binary
   words of length `k`. Then `br(r_k) = 2^k`.
4. Consequently, for any finite `S ⊂ V` with `b_S = max_(s ∈ S) (br(s) − 1) > 0`,
   every word in `S^(±1)` and arbitrary elements of F that represents `r_k`
   contains at least `(2^k − 1)/b_S` letters from `S^(±1)` outside F. For
   Lorrain's generators `x_0, x_1, c_1, π_0` this is a linear lower bound on the
   number of `c_1^(±1), π_0^(±1)` letters.
5. Contrast: `br(t) ≤ 2` for every `t ∈ T`.

**What this kills.** Migliorini's Proposition 4.2 (arXiv:2410.23088) writes
every `f ∈ T \ F` as `u(S_F) · C_0 · v(S_F)`, with one non-F letter. No normal
form for V with a bounded number of non-F letters exists, so that step of the T
proof does not transfer. Migliorini's §6 names this obstacle; the break count
above proves it and quantifies it. His Proposition 4.3 (the triangle criterion)
is not affected.
