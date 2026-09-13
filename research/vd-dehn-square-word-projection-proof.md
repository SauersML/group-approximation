---
rg: 2
id: vd-dehn-square-word-projection-proof
kind: route
title: Fill in the CAT(0) expansion complex, then project every square to a standard square word
target: vd-dehn-bounded-by-standard-square-word-area
requires:
  - vd-expansion-cube-complex-is-cat0
  - cat0-cube-loops-bound-quadratic-square-diagrams
---

Notation as in the claim. `h` is the height, and `v_0` the height-one vertex
`[id]`.

**(P1) Boundary loop.** For each `s ∈ S` fix an edge path `p_s` in `K_d` from
`v_0` to `s·v_0`. Such paths exist because `K_d` is connected (import 1). Let
`k_0` be the largest height they visit. A null-homotopic word
`w = s_1 ⋯ s_L` gives the loop `γ = p_(s_1) · (g_1 p_(s_2)) ⋯ (g_(L-1) p_(s_L))`,
with `g_i = s_1⋯s_i`. It has length `L' <= c·L` and heights `<= k_0`.

**(P2) Filling.** By import 1, `K_d` is a CAT(0) cube complex. By import 2, `γ`
bounds a square disc diagram `D` with at most `L'^2/8` squares.

**(P3) Heights.** Let `x` be a vertex of `D` and `b` a boundary vertex. Every
hyperplane of `K_d` separating `x` from `b` meets the image of `D`, so by import
2 it meets `γ`. There are at most `L'/2` such hyperplanes. Combinatorial
distance in a CAT(0) cube complex is the number of separating hyperplanes, and
every edge changes height by exactly `d - 1`. Hence
`h(x) <= k_0 + (d-1)L'/2`.

**(P4) Projection of the interior.** Orient each edge of `D` upward in height
and replace it by `W(e)`. Around each square the four words form a square word
`q ∈ Q_n`, where `n` is the height of the square's lowest corner. The product of
the edge words along `∂D` is therefore a product of conjugates of these square
words, one for each square. So the projected boundary word `w_γ` satisfies
`Area(w_γ) <= (L'^2/8) · max_{n <= k_0 + (d-1)L'/2} A_d(n)`.

**(P5) Boundary conversion.** For `x` of height `<= k_0` and `g ∈ V_d`,

```text
r(g·x) = g · r(x) · ε(g,x),   ε(g,x) = s_n ∘ o_x^(-1) o_(g·x) ∘ s_n^(-1),
```

a permutation of the standard pieces. With `n <= k_0` there are finitely many
values of `ε`, and `ε = 1` at height one. So the projection of `g·p_s` is one
of finitely many words, each representing `s`, because `r(g·v_0) = g` and
`r(g s·v_0) = g s`. Converting `w` letter by letter to `w_γ` therefore costs
`O(L)` area.

**Conclusion.** `Area(w) <= C·L + C·L^2 · max_{n <= k_0 + C·L} A_d(n)`, which is
the claim.

**Checks inside the route.**
- `r` is well defined: reordering the components of `φ` changes `o_v`
  compatibly.
- Edge and square types are finite for each `n`: the combinatorial type of
  `o_v^(-1) σ o_(v')` is a split position plus an interleaving permutation.
- Every 2-cell of `D` is a square of `K_d`, so it is two splits of distinct
  pieces.
