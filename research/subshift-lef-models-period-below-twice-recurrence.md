---
rg: 2
id: subshift-lef-models-period-below-twice-recurrence
kind: claim
title: Periodic LEF models of a minimal subshift have period below twice its recurrence function, which bounds the LEF growth of G_X
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that proves the periodic models exist and give an ultraproduct embedding; this bounds their period explicitly and converts group radius into model size
  elementary-group-lef-growth-separates-subshifts: that is the open two-sided growth classification; this is the explicit upper bound whose radius-to-window dictionary that node lists as missing
artifacts:
  - research/artifacts/sk-lef-short-proposal-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Route `subshift-lef-models-period-below-twice-recurrence-proof`.

Let `X ⊆ A^Z` be an infinite minimal subshift. Write `L_n(X)` for its words of length `n` and `p_X(n) = |L_n(X)|`.
Let `Rec_X(n)` be the least `m` such that every word in `L_m(X)` contains every word in `L_n(X)`. It is finite by
minimality.

1. **Periodic models.** For every `k >= 0` there are `N_k` and an `N_k`-periodic `y_k ∈ A^Z` with
   `L_(2k+1)(y_k) = L_(2k+1)(X)` and
   `p_X(2k+1) <= N_k <= 2 Rec_X(2k+1) - 4k`,
   so `2k+2 <= N_k < 2 Rec_X(2k+1)`.
2. **Ball dictionary.** Let `R = LC(X,F_q) ⋊ Z` and `G = EL_3(R)`, with a finite symmetric generating set of
   elementary matrices `e_ij(λ s)`, where `λ ∈ F_q` and `s ∈ {1, u, u^(-1)} ∪ {e_a : a ∈ A}`. For every `r >= 1`
   there is an injective map `B(r) → GL_(3N)(F_q)` with `N = N_(2r) < 2 Rec_X(4r+1)`, preserving every product `gh`
   of `g, h ∈ B(r)` that lies in `B(r)`. So the LEF growth of
   `elementary-group-lef-growth-separates-subshifts` satisfies
   `F(r) <= |GL_(3N)(F_q)| < q^(9N^2) < q^(36 Rec_X(4r+1)^2)`.
3. **Linearly recurrent `X`.** If `Rec_X(n) <= L n`, then `F(r) < q^(36 L^2 (4r+1)^2) = q^(O(r^2))`. Primitive
   substitution subshifts, e.g. Fibonacci, are linearly recurrent (Durand, recalled, not re-verified here).

This is only an upper bound. The matching lower bound, which would pin `F(r) = q^(Θ(r^2))` for linearly recurrent
`X`, belongs to `elementary-group-lef-growth-separates-subshifts`.
