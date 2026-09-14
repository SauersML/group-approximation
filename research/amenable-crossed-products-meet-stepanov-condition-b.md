---
rg: 2
id: amenable-crossed-products-meet-stepanov-condition-b
kind: claim
title: In a crossed product LC(X,K) ⋊ Γ by an amenable group any two elements satisfy a nontrivial right linear relation, so Stepanov's condition (b) holds
distinct_from:
  division-rings-satisfy-stepanov-b-not-local-annihilation: that verifies Stepanov's (b) for simple Artinian rings; this verifies it for crossed products of totally disconnected spaces by amenable groups, by a dimension count on one cylinder.
  local-annihilation-implies-stepanov-condition-b: that asks whether local annihilation implies (b) for every simple ring; this proves (b) directly for amenable crossed products and uses no annihilation.
artifacts:
  - research/artifacts/sk-stable-rank-b-stepanov-route-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `K` be a field and `Γ` an amenable group acting by homeomorphisms on a compact
totally disconnected space `X`. Put `R = LC(X,K) ⋊ Γ`, the finite sums `Σ_γ f_γ u_γ` with `f_γ` locally constant and
`u_γ f u_γ^{-1} = f∘γ^{-1}`. The action need not be minimal or free.

1. **Pair dependence.** For `p, q ∈ R` there are `r, s ∈ R`, not both `0`, with `pr + qs = 0`.
2. **Stepanov's condition (b).** Let `n ≥ 3` and `a ∈ GL_n(R)`. Apply item 1 to `p = a_12` and `q = a_13`, and put
   `α = (0, r, s, 0, …, 0)^T`. Then `α ≠ 0` and `α_1 = (aα)_1 = 0`. This is condition (b) of Stepanov's Theorem 4.4
   (`stepanov-linear-dependence-standard-normal-structure`) for the ideal `I = 0`, with `b = 1` and `i = j = 1`.

For `Γ = Z` the count is explicit. If the exponents of `p` and `q` lie in `[−w, w]`, the relation uses `r, s` supported
on `u^0, …, u^{2w}` over one small cylinder `U`, since `2(2w+1) > 4w+1`.

**Model tests.**
- Commutative rings satisfy item 1 with `r = q` and `s = −p`. Simple Artinian rings satisfy it by
  `division-rings-satisfy-stepanov-b-not-local-annihilation`.
- Item 1 fails when `R` contains a Leavitt family, i.e. elements `s_0, s_1, t_0, t_1` with `t_i s_j = δ_ij`. Then
  `s_0 r + s_1 s = 0` gives `r = t_0(s_0 r + s_1 s) = 0` and likewise `s = 0`. That happens for the boundary crossed
  products `LC(∂F_d,K) ⋊ F_d`. There `Γ` is not amenable, and the count dies at `|SF| < 2|F|`.

Consequence: `subshift-elementary-group-simple-stepanov-proof`.
