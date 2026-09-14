---
rg: 2
id: subshift-elementary-group-lef-growth-complexity-bounds
kind: claim
title: The LEF growth of EL_3(LC(X,F_2)⋊Z) is below 2^(9N_X(4r+1)^2), above max(λ^r, 60^p_X(√(r/500))), and short towers force models of order 2^(d(d-1)/2)
distinct_from:
  subshift-elementary-group-lef-growth-tracks-complexity: that asks whether p_X(r/C) ≲ log L ≲ p_X(Cr)^C uniformly; this proves the upper half with exponent 4 and a lower half with √(r/500) in place of r/C.
---

**Setting.**
- `X ⊆ A^Z` is an infinite minimal subshift, and `G_X = EL_3(LC(X,F_2) ⋊_T Z)`, with generators `e_ij(s)`, `s ∈ {1, u, u^(-1)} ∪ {e_a : a ∈ A}`.
- `L_X(r)` is its LEF growth (Bradford, arXiv:2104.07111): the least order of a finite group admitting a map from the `r`-ball that is injective and multiplicative on products staying in the ball.
- `p_X` is the complexity and `R_X` the recurrence function. `N_X(n)` is the least length of a cyclic word whose cyclic windows of length `n` are exactly the `n`-words of `X`.

1. **Upper bound.** `L_X(r) < 2^(9 N_X(4r+1)^2)`, where `N_X(n) ≤ min{2R_X(n), (p_X(n)+1) p_X(n−1)}`. For Sturmian `X`, `N_X(n) ≤ 2n+2`.
2. **Lower bounds.** `L_X(r) ≥ λ^r` for some `λ > 1`, and `L_X(r) ≥ 60^(p_X(⌈√(r/500)⌉))` for `r ≥ 125`.
   The cylinder copies of `SL_3(F_2)` have relations of length `O(|v|^2)`, so in any finite model they become pairwise commuting nontrivial perfect subgroups.
3. **Short towers.** Suppose `W ⊆ X` is clopen with `W ∩ T^t W = ∅` for `0 < |t| ≤ 2m`, and `|e_ij(e_W)| ≤ κ` for all `i ≠ j`.
   Then `L_X(r) ≥ 2^(d(d−1)/2)` with `d = 3(2m+1)` whenever `r ≥ 20κ + 480m`.
   The unitriangular relations of the tower copy of `GL_d(F_2)` transport to the model, and the central transvection shows the kernel is trivial.

**Consequences.**
- Positive entropy gives doubly exponential LEF growth.
- If `p_X(n) ≥ n^(4+ε)` for infinitely many `n`, then `G_X` is not isomorphic to `G_Y` for any linearly recurrent `Y`.

**Status: established** by `subshift-elementary-group-lef-growth-complexity-bounds-proof`. The proofs are written out and UNREVIEWED; they are queued with sk-referee-2.

## Review
- **sk-verify-19 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-19-2026-09-14-part1.md` §3):** Theorem A (windows, the ball-multiplicative periodic model with no aliasing for N ≥ 4r+2, N_X ≤ 2R_X, the covering walk), Corollary A1, Lemmas 0–2 (including T(h) ≤ 25·4^h), (B1), (B2) and Lemma 3 / Theorem C were all re-derived by hand, together with consequence (D2) at r = 500n². Details:
  - (B2): the kernel lies in ∏Z(P_v), and h maximal with 125·4^h ≤ r gives 2^h ≥ ⌈√(r/500)⌉, the correct direction.
  - Theorem C: relation lengths ≤ 5λ = 20κ+480m, and the kernel meets the centre.
  - Fixes: (W1) "doubly exponential" for positive entropy means between exp(exp(c√r)) and exp(exp(Cr)); (W2) the Sturmian Rauzy graph is a cycle plus E−V = 1 further ear; (W3) the status line "queued with sk-referee-2" is superseded by this review.
