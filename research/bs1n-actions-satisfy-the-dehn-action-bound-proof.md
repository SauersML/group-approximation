---
rg: 2
id: bs1n-actions-satisfy-the-dehn-action-bound-proof
kind: route
title: "Finite index, exponential distortion, or finite clusters: the three cases for actions of BS(1,q)"
target: bs1n-actions-satisfy-the-dehn-action-bound
requires:
  - finite-infinite-stabilizer-clusters-give-dehn-bound
artifacts:
  - research/artifacts/zp-dehn-finite-cluster-collapse-2026-09-17.md
---

The full argument is in §5 of
`research/artifacts/zp-dehn-finite-cluster-collapse-2026-09-17.md`. Write
`G = A ⋊ ℤ` with `A = ℤ[1/q]`, `π : G → ℤ` and
`(a, s)(b, r) = (a + q^s b, s + r)`. Let `H = G_x` run over the vertex
stabilizers.

1. **Case 1: `H ∩ A ≠ 0` and `π(H) ≠ 0`.**
   - Conjugating `(u, 0)` by `(w, k)^j` gives `H ∩ A ⊇ u ℤ[1/q]`, which has
     finite index in `A`. So `[G : H] < ∞`.
   - `δ_H ≃ δ_G` (Alonso 1990). Under (N), the right-hand side of (UB) is
     `≥ δ_H(n)`.
2. **Case 2: `1 ≠ H ≤ A`.**
   - `H` is finitely presented, so it is cyclic, `H = ⟨u⟩`.
   - `t^j u t⁻ʲ = u^{q^j}` gives `dist_X(n) ≽ e^n`. Under (N), the right-hand
     side of (UB) is `≥ dist_X(n)`.
   - `δ_G ≼ e^n`. Freely rewrite a relation as at most `n` conjugates of
     `a^{±1}` by `t^p`, `0 ≤ p ≤ 2n`, after conjugating by `t^n`. Each costs
     `≤ q^p` relators to become `a^{±q^p}`.
3. **Case 3: every `H` meets `A` trivially.**
   - Every `H` is trivial or `⟨(w, k)⟩` with `k ≠ 0`, so nested infinite
     stabilizers have finite index.
   - `A ∩ Comm_G(H) = 0`: an element `(v, 0)` commuting with `h^m` has
     `v(1 − q^{mk}) = 0`. So `[Comm_G(H) : H] ≤ |k|`.
   - Corollary B of `finite-infinite-stabilizer-clusters-give-dehn-bound` shows
     that `X_∞` has finite components. The vertex groups are trivial or `ℤ`,
     with doubling normalized Dehn function `m`. So the doubling form of that
     claim gives (UB) for every generating set.

Cases 1 and 2 are elementary and use no generating-set-dependent constant.
