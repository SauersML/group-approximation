---
rg: 2
id: leavitt-resolvent-frame-complex-is-highly-connected
kind: claim
title: The ordered frame complex X_r(R_L) is (r-3)-acyclic and simply connected for r >= 4, and E_r(R_L) acts transitively on its frames of size at most r-1, by a simultaneous word multiplier built from separated vacuum isometries
distinct_from:
  leavitt-resolvent-frame-complex-route-to-injective-stability: that lists simple connectivity (F) as an open input of the route to condition (i); this proves (F), leaving the characteristic-0 presentation step.
  leavitt-ge-rings-have-stable-k1-at-rank-three: that proves the compression y x z = 1 and GL_r(R_L)/E_r(R_L) = Z; this uses both, for the frame multiplier and for E_r-transitivity.
---

**ESTABLISHED** through `leavitt-resolvent-frame-complex-is-highly-connected-proof`. Lane proof, not independently
reviewed. The cone and fan arguments are Khanh's (arXiv:2609.08428, Proposition `prop:frame-cone`, Corollary
`cor:frame-homology`, and the fan in the proof of Theorem `thm:steinberg-isomorphism`, read in TeX). What is new is
the multiplier for `R_L`, which replaces Khanh's argument over `F_2`. No priority is claimed.

**Setting.** `X_r(R)` is Khanh's ordered frame complex. A `(k-1)`-simplex is an ordered tuple `(v_1, ..., v_k)`,
`k <= r`, with `R^r = v_1 R ⊕ ... ⊕ v_k R ⊕ C`, `C ≅ R^(r-k)`, and each `b -> v_i b` injective. Words in `s_1, s_2` are
written `s_η`, and `t_η = s_η*`.

**Statement.**
1. **Simultaneous multiplier.** For nonzero `a_1, ..., a_q in R_L` there are `x in R_L` and nonempty words `η_1, ..., η_q`
   with `t_(η_i) a_i x = 1` for every `i`.
2. **Frame cones.** Every finite family of simplices of `X_r(R_L)`, each with at most `r - 2` vectors, has a single
   common extension vector `v`. Every extended frame has a nonzero complement of the prescribed formal size.
3. **Connectivity.** `H̃_d(X_r(R_L); Z) = 0` for `0 <= d <= r - 3`, and `|X_r(R_L)|` is simply connected for `r >= 4`.
4. **Transitivity.** For `r >= 4` and `k <= r - 1`, `E_r(R_L)` acts transitively on ordered `k`-frames.

## Consequence for the route to condition (i)

Input (F) of `leavitt-resolvent-frame-complex-route-to-injective-stability` holds for `n >= 4`, with `E_n` acting
transitively on vertices, edges and triangles. Input (S1) holds by `leavitt-ge-rings-have-stable-k1-at-rank-three`.
What remains is the characteristic-`0` form of the Brown presentation. Over `F_2`, Khanh uses `T^2 = 1`. Here the
signed transposition has `T^2 = diag(-1, -1, 1, ...)`, which sends the vertex `b_1` to `-b_1`, so the presentation needs
one more relation, and its lift in `St_n` has to be matched modulo the central `C`.
