---
rg: 2
id: brin-thompson-2v-three-pass-baker-obstruction-proof
kind: route
title: "Row-column-row rearrangement by Hall's theorem for grid permutations; the fibre transport h_*(2^{c_y(h)} mu) for the obstruction"
target: brin-thompson-2v-three-pass-fibre-products-miss-the-baker-map
requires: []
---

Notation is as in the target. Every `h ∈ 2V` is a canonical brick map for some pair of brick
partitions. Hence `c_x(h,·)` and `c_y(h,·)` are locally constant. For `v ∈ V` write `c_v` for
the base-2 log-derivative.

**Step 0 (one-dimensional mass formula).** Take `v ∈ V` and a clopen `S ⊆ C`. Then
`λ(v(S)) = ∫_S 2^{c_v} dλ`. To see this, cut `S` into cones on which `v` acts as `bu ↦ du`. On
such a cone `λ([d]) = 2^{|b|−|d|} λ([b])` and `c_v = |b| − |d|`. Both sides are additive in `S`.

**Step 1 (cocycle).** On a common refinement of the partitions, each map is a canonical
translation on each piece. The chain rule then gives `c_y(gh,p) = c_y(g,hp) + c_y(h,p)`, and
`c_y(id) = 0`. For a finite Borel measure `μ` on `C²` put

```text
T_h μ = h_*(2^{c_y(h,·)} μ),   i.e.   (T_h μ)(A) = ∫_{h^{-1}A} 2^{c_y(h,p)} dμ(p).
```

Then `T_{gh} = T_g T_h`, `T_{id} = id` and `T_{h^{-1}} = T_h^{-1}`. Each `T_h` maps
full-support measures to full-support measures, because `h` is a homeomorphism and the weight is
positive.

**Step 2 (`L_1` preserves `y`-marginals).** For `l ∈ L_1`, `c_y(l,·) ≡ 0`, so `T_l μ = l_*μ`.
Since `l` preserves every horizontal line `C × {y}`, `(l_*μ)(C × E) = μ(l^{-1}(C × E)) = μ(C × E)`.

**Step 3 (`L_2` fixes `λ ⊗ λ`).** Let `m(x,y) = (x, G(x)y)` with `G = v` constant on the cone
`[α]`. For a clopen `E ⊆ C`:
- `m^{-1}([α] × E) = [α] × v^{-1}E`, and `c_y(m,(x,y)) = c_v(y)` there;
- by Step 0 with `S = v^{-1}E`, `(T_m(λ⊗λ))([α]×E) = λ[α] · ∫_{v^{-1}E} 2^{c_v} dλ = λ[α] λ(E)`.

Sets `[α']×E` with `[α'] ⊆ [α]` generate, and finitely many cones `[α]` cover `C`. Hence
`T_m(λ⊗λ) = λ⊗λ`.

**Step 4 (the transport invariant, part 2).** Let `g = l_1 m l_2`, with `l_i ∈ L_1` and
`m ∈ L_2`. Put `μ = T_{l_2}^{-1}(λ⊗λ) = (l_2^{-1})_*(λ⊗λ)`.
- `μ` is a probability measure with full support.
- By Step 2 its `y`-marginal is `λ`.
- By Steps 1 to 3, `T_g μ = T_{l_1} T_m (λ⊗λ) = T_{l_1}(λ⊗λ)`, whose `y`-marginal is `λ` (Step 2).
- So `1 = (T_g μ)(C²) = ∫ 2^{c_y(g,p)} dμ(p)`.

**Step 5 (obstruction, part 3).** Suppose `c_y(g,·) ≤ 0` everywhere and `c_y(g,·) ≠ 0`
somewhere. Then `c_y(g,·) ≤ −1` on a nonempty clopen set, which has positive `μ`-measure. So
`∫ 2^{c_y(g)} dμ < 1`, contradicting Step 4. The case `≥ 0` is symmetric.

Now the baker map. On `[x_1] × C`, `β(x_1 u, v) = (u, x_1 v)`, so its `y`-derivative is `1/2`
and its `x`-derivative is `2` everywhere. Hence for `N ≥ 1`:
- `c_y(β^N) ≡ −N` (Step 1), so `β^{±N} ∉ L_1 L_2 L_1`;
- `α L_2 L_1 L_2 α = L_1 L_2 L_1` and `c_y(αhα, p) = c_x(h, αp)`;
- since `c_x(β^{±N}) ≡ ±N ≠ 0`, `αβ^{±N}α ∉ L_1 L_2 L_1`, that is, `β^{±N} ∉ L_2 L_1 L_2`.

**Step 6 (part 1: `V × V` and grid permutations).** First, `v × w = (v × 1)(1 × w)`, with
`v × 1 ∈ L_1` (constant `F`) and `1 × w ∈ L_2` (constant `G`).

Now fix `p, q` and a permutation `π` of the cells `[a]×[b]`, where `|a| = p` and `|b| = q`. Let
`k ∈ K` translate each cell canonically onto its image. Call the `2^q` sets `C × [b]` *rows* and
the `2^p` sets `[a] × C` *columns*.
- A *row pass* permutes the cells inside each row by canonical translations. It lies in `L_1`:
  on `y ∈ [b]`, `F(y)` is the permutation of the depth-`p` cones used in row `b`.
- A *column pass* likewise lies in `L_2`.

Build a bipartite multigraph:
- vertices: source rows `b` and target rows `b'`;
- one edge per cell `[a]×[b]`, joining `b` to the row of `π([a]×[b])`.

It is `2^p`-regular. So for a set `S` of source rows, the `2^p|S|` edges at `S` all meet `N(S)`,
which carries at most `2^p|N(S)|` edges, giving `|N(S)| ≥ |S|`. By P. Hall's marriage theorem
there is a perfect matching. Removing it leaves a `(2^p − 1)`-regular graph, and induction
splits the edges into `2^p` perfect matchings `M_a`, indexed by the depth-`p` words `a`.

Then `k = R_3 C_2 R_1`:
1. `R_1` (row pass) moves, in each source row, the cell whose edge lies in `M_a` to column `a`.
   This is a bijection within the row, since each row has exactly one edge in each `M_a`.
2. `C_2` (column pass) moves, inside column `a`, each cell to its target row. This is a
   bijection, since `M_a` is a perfect matching.
3. `R_3` (row pass) moves, inside each target row, each cell to its target column.

Each pass is a composite of canonical translations, and so is `k`. So `k ∈ L_1 L_2 L_1`. ∎
