---
rg: 2
id: stabilized-kgraph-full-group-clopen-action-proof
kind: route
title: The Cuntz factor halves every clopen set, so homology vanishes; Matui's comparison then makes clopen sets with the same pattern equivalent, which gives finitely many orbits of pairs and full-group stabilizers
target: stabilized-kgraph-full-groups-have-type-a-actions
requires: [type-a-action-gives-boone-higman-for-subgroups, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation as in the target. Clopen sets `U, W ⊆ C''` are *equivalent*, `U ~ W`, if
some compact open bisection of `𝒢''` has source `U` and range `W`.

**Step 1 (item 1).** The product of a `k`-graph and a 1-graph is a `(k+1)`-graph
whose boundary groupoid is the product groupoid (Kumjian--Pask; not re-read).
`Λ x O_2` is finite, and has at least two loops of every colour at every vertex:
those of `Λ` in colours `1..k`, the two `O_2` loops in colour `k+1`. `C''` is the
union of the boundaries of the distinct vertices `(v, *)` with `∂Λ(v) ⊆ Z`. So Li's
theorem `thm:k-graphs` (arXiv:2110.04505v2, l.2124, read at source) makes `D` of
type `F_∞`. For `g ∈ F(𝒢)`, `g x id` is locally given by products of
bisections of `𝒢` with units of `𝒢_(O_2)`, so it lies in `D`. The map is
injective.

**Step 2 (item 2).** Every clopen `U ⊆ C''` is a finite disjoint union of products
`A_s x [w_s]`, with `A_s` clopen in `Z` and `[w_s]` a cylinder of `{0,1}^N`. Put
`U_i = ⊔_s A_s x [w_s i]` for `i = 0, 1`. Then `U = U_0 ⊔ U_1`, and
`(a, w_s y) ↦ (a, w_s i y)` is a compact open bisection from `U` onto `U_i`. So
`U` is properly infinite, and `[U] = [U_0] + [U_1] = 2[U]`, so `[U] = 0`. Classes of
clopen sets generate `H_0(𝒢'')`, so `H_0(𝒢'') = 0`.
- **Effective.** The isotropy of `(x, y)` is the product of the isotropies.
  Points with trivial isotropy are dense in each factor (both are effective and
  second countable), hence in the product.
- **Minimal pieces.** If `Z = ⊔_t Z_t` is the given decomposition, then the pieces
  `C''_t = Z_t x {0,1}^N` are clopen and invariant, and `𝒢''` is minimal on each,
  because `𝒢_(O_2)` is minimal.

**Step 3 (comparison).** Matui's comparison theorem for second countable, effective,
minimal, purely infinite ample groupoids: nonempty clopen sets with equal
`H_0`-class are equivalent (H. Matui, J. reine angew. Math. 705 (2015), §4;
cited, not re-read). Apply it on each `C''_t`. By Step 2, any two nonempty
clopen subsets of the same `C''_t` are equivalent.

**Step 4 (item 3).** Let `S` be the set of nonempty proper clopen subsets of
`C''`. It is countable.
- **Faithful.** Clopen sets separate points.
- **Pairs.** For `U, W ∈ S`, consider the four Boolean atoms of `(U, W)` and record
  which atoms meet which `C''_t`. If `(U, W)` and `(U', W')` have the same record,
  then each nonempty atom piece is equivalent to the corresponding one (Step 3),
  and the bisections glue to a compact open bisection with source and range
  `C''`, that is, an element of `D` carrying `(U, W)` to `(U', W')`. There are
  finitely many records, so there are finitely many orbits of 2-element subsets.
- **Stabilizers.** `D` preserves each `C''_t`, so `D = ∏_t F(𝒢''|_(C''_t))`, and
  each factor, as a retract of a finitely presented group, is finitely presented.
  The stabilizer of `U ∈ S` is `F(𝒢''|_U) x F(𝒢''|_(C'' \ U))` (a stabilizer
  element splits into its restrictions, each in the full group). For a nonempty
  `U ∩ C''_t`, a bisection onto `C''_t` (Step 3) conjugates
  `F(𝒢''|_(U ∩ C''_t))` onto `F(𝒢''|_(C''_t))`. So the stabilizer is a product
  of finitely many finitely presented groups, hence finitely generated.
- **Finite presentation.** `D` is finitely presented by Step 1.
So the action is of type (A).

**Step 5 (item 4).** By `type-a-action-gives-boone-higman-for-subgroups`, every
subgroup of `D` has solvable word problem and embeds in a finitely presented
simple group. So `D ∈ B_A`, and so is its subgroup `F(𝒢)` (item 1 of
`boone-higman-type-a-class-closed-under-finite-extensions`).
