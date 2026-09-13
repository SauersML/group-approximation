---
rg: 2
id: rover-nekrashevych-characters-are-sum-invariant-proof
kind: route
title: Sum the local group labels of a table; refinement invariance is exactly sum-invariance over sections
target: rover-nekrashevych-characters-are-sum-invariant
requires: []
---

Notation as in the claim. Sections satisfy `g(xw) = g(x) g|_x(w)`,
`(gh)|_x = g|_{h(x)} h|_x`, and `g|_{xy} = (g|_x)|_y`. A *table* of `h in V_d(G)` is a list of
pieces `(u_i -> v_i, g_i)` with `{u_i C}` and `{v_i C}` cone partitions and `h(u_i w) = v_i g_i(w)`.
*Refining* piece `i` at `x in X` replaces it by the `d` pieces `(u_i x -> v_i g_i(x), g_i|_x)`.
Every finite cone partition of a cone arises by iterated splitting, so refining a piece
along a complete prefix code `Z` gives the pieces `(u_i z -> v_i g_i(z), g_i|_z)`, `z in Z`.

**Step 1 (`ψχ` is a homomorphism).** `Σ_x χ((gh)|_x) = Σ_x χ(g|_{h(x)}) + Σ_x χ(h|_x) = ψχ(g) + ψχ(h)`,
because `h` permutes `X`.

**Step 2 (tables are unique up to refinement).** Refine two tables of `h` to the same domain
partition. On a common piece `uC` we get `v g(w) = v' g'(w)` for all `w in C`. Suppose `|v| <= |v'|` and
write `v' = v z`. Then `g(C) ⊆ zC`, and `g` is onto `C`, so `z` is empty. Hence `v = v'` and `g = g'` on `C`,
so `g = g'` because the action is faithful.

**Step 3 (`Φ_χ` is well defined when `ψχ = χ`).** Refining piece `i` at `x` replaces `χ(g_i)` by
`Σ_x χ(g_i|_x) = ψχ(g_i) = χ(g_i)`. So `Σ_i χ(g_i)` is refinement invariant, and by Step 2 it depends only on `h`.

**Step 4 (`Φ_χ` is a homomorphism).** Take tables `(u_i -> v_i, g_i)` of `k` and `(u'_j -> v'_j, f_j)` of `h`.
Refine the first until every `v_i C` lies in some `u'_j C`, and write `v_i = u'_j z_i`. Then
`h(k(u_i w)) = v'_j f_j(z_i) f_j|_{z_i}(g_i(w))`, so `(u_i -> v'_j f_j(z_i), f_j|_{z_i} g_i)` is a table of `hk`.
Hence `Φ_χ(hk) = Σ_i χ(g_i) + Σ_j Σ_{i: v_i C ⊆ u'_j C} χ(f_j|_{z_i})`. For fixed `j`, the `z_i C` form a
cone partition of `C`, so the inner sum is the refinement of piece `j` of `h` along a prefix code. By
Step 3 the double sum equals `Φ_χ(h)`. So `Φ_χ(hk) = Φ_χ(h) + Φ_χ(k)`.

**Step 5 (the two maps are inverse).** If `ψχ = χ`, then `g_(u)` has the table `(u -> u, g)` plus identity
pieces on a cone partition of `C \ uC`, so `Φ_χ(g_(u)) = χ(g)`. Conversely, let `Φ in Hom(V_d(G), R)`.

- (a) `Φ(V_d) = 0`: the Higman–Thompson group `V_d = V_{d,1}` has finite abelianization (Higman 1974;
  also item (Ab) of `rover-nekrashevych-finite-presentation-criteria` with trivial `H`).
- (b) Independence of `u`. For nonempty `u, u'` the complements `C \ uC` and `C \ u'C` are unions of
  `|u|(d-1)` and `|u'|(d-1)` cones. Splitting a cone adds `d-1` cones, so both complements admit cone
  partitions with the same number of pieces. Mapping those bijectively by prefix replacement, and
  `uw -> u'w` on `uC`, gives `t in V_d` with `t g_(u) t^{-1} = g_(u')`. So `χ(g) := Φ(g_(u))` does not
  depend on `u`, and it is a homomorphism because `g -> g_(u)` is.
- (c) `ψχ = χ`. We have `g_(u) = s ∘ Π_{x in X} (g|_x)_(ux)`, where `s in V_d` sends `uxw -> u g(x) w` and is
  the identity off `uC`. Indeed `(g|_x)_(ux)` sends `uxw -> ux g|_x(w)`, then `s` gives `u g(x) g|_x(w) = u g(xw)`.
  The factors have disjoint supports. By (a) and (b), `χ(g) = Σ_x χ(g|_x)`.
- (d) `Φ = Φ_χ`. Refine any table of `h` once, so every `u_i` is nonempty. Then
  `h = s ∘ Π_i (g_i)_(u_i)` with `s in V_d` the prefix replacement `u_i w -> v_i w`. So `Φ(h) = Σ_i χ(g_i) = Φ_χ(h)`.

Both maps are linear, so they are inverse linear isomorphisms. ∎

**Model tests.**

- Trivial `G`: the only fixed character is `0`, matching Higman's finite abelianization.
- Binary odometer `a = σ(1, a)`: `ψ` is the identity on `Hom(Z, R)`. `Φ_χ` counts total `a`-exponent;
  refinement replaces `a^n` on a cone by `a^{⌈n/2⌉}` and `a^{⌊n/2⌋}` on the two subcones, and the exponent sum `n` is preserved.
