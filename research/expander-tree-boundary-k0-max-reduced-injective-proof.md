---
rg: 2
id: expander-tree-boundary-k0-max-reduced-injective-proof
kind: route
title: Large girth puts every tree-boundary support in the CND-support shift, where max to reduced is an isomorphism
target: expander-tree-boundary-k0-max-reduced-injective
requires:
  - cnd-support-shift-bc-and-k-amenability
artifacts:
  - research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md
---

Full argument: `research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Lemma 1.1 and Section 5 (Theorem C).
Hypotheses (M) are those of `hls-ghost-lift-needs-forest-shift-failure`; only the definitions are used. `d` is the word
metric, `x_n = 1_(A_n)`, `U = ∪_n G·x_n`, `Ŷ = closure(U)` and `∂Y = Ŷ \ U` in `X = (Z/p)^G`.

1. **`∂Y \ {0}` is closed in `X^0` and invariant (artifact, Lemma 1.1).**
   - The subgraph of `Cay(G, S)` induced on each `g A_m` is connected, since edges of `X_m` go to word distance `1`.
   - If `g A_m ⊇ A_n` and `g A_m` misses the outer boundary `N_n \ A_n`, connectedness gives `g A_m = A_n`. Then `m = n`
     because the sizes strictly increase, and `g = e` because torsion-free groups fix no finite nonempty set.
   - If a limit `lim g_i x_(n_i) ≠ 0` has a subsequence with `n_i` constant, the `g_i` range over a finite set and the
     limit lies in `U`.
   - Together these show that the cylinder `{z ∈ Ŷ : z = x_n on N_n}` is `{x_n}`. So `U` is open in `Ŷ`, and `∂Y` is
     closed and invariant.
2. **Balls in large girth (artifact, Lemma 5.1).** If `girth(Γ) > 2R + 1`, the ball `B(v, R)` of a graph `Γ` induces a
   tree: a non-tree edge of a breadth-first tree would close a cycle of length at most `2R + 1`.
   - If `diam_Γ(F) <= r` and `girth(Γ) > 4r + 1`, geodesics between points of `F` stay in `B(f_0, 2r)`, which induces a
     tree `T`. So `d_Γ = d_T` on `F`.
   - Tree metrics are CND. Concretely `d_T(u, w) = ||ξ_u - ξ_w||^2`, where `ξ_u` is the indicator vector of the edges
     separating `u` from `f_0`.
3. **Supports of boundary points are CND.**
   - Let `y ∈ ∂Y \ {0}` and `F ⊆ supp y` finite with `diam_d(F) = r`. Write `y = lim g_i x_(n_i)`. By step 1,
     `n_i -> ∞`.
   - For large `i`, `F ⊆ g_i A_(n_i)` and `girth(X_(n_i)) > 4r + 1`.
   - `d` restricted to `A_(n_i)` is the path metric of `X_(n_i)`. So by step 2, `d` restricted to `g_i^(-1) F` is CND,
     hence so is `d` restricted to `F`.
   - So `∂Y \ {0} ⊆ T_cnd \ {0}`.
4. **Conclusion.** Apply `cnd-support-shift-bc-and-k-amenability`, item 3, to `Z = ∂Y \ {0}`.
   `K_*(C_0(∂Y \ {0}) ⋊_max G) -> K_*(C_0(∂Y \ {0}) ⋊_r G)` is an isomorphism in both degrees, so it is injective on
   `K_0`. Items 1 and 2 also give that `mu_(G, C_0(∂Y \ {0}))` is an isomorphism. QED.

**Remark.** The stopping point recorded in the target, the lack of canonical nearest-point projections, is avoided. The
basepoint is an arbitrary locally constant choice of a support point, and all the geometry enters through CND of the word
metric on single supports.
