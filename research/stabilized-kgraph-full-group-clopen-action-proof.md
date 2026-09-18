---
rg: 2
id: stabilized-kgraph-full-group-clopen-action-proof
kind: route
title: Refining cylinder decompositions spreads every clopen set over its whole strongly connected piece, the Cuntz colour then equalizes counts, and that comparison gives a type (A) action on clopen sets
target: stabilized-kgraph-full-groups-have-type-a-actions
requires: [type-a-action-gives-boone-higman-for-subgroups, boone-higman-type-a-class-closed-under-finite-extensions, li-finite-k-graph-full-groups-are-f-infinity]
---

Notation as in the target. Clopen sets `U, W ⊆ C''` are *equivalent*, `U ~ W`, if
some compact open bisection of `𝒢''` has source `U` and range `W`. Paths `λ` of
`Λ'' = Λ x O_2` have range `r(λ)` and source `s(λ)`, and the cylinder `Z(λ)` is a
copy of `∂Λ''(s(λ))` through `x ↦ λx`.

**Step 1 (item 1).** The product of a `k`-graph and a 1-graph is a `(k+1)`-graph
whose boundary groupoid is the product groupoid (Kumjian--Pask; not re-read).
`Λ''` is finite, with at least two loops of every colour at every vertex: those
of `Λ` in colours `1..k`, the two `O_2` loops in colour `k+1`. `C''` is the union
of the boundaries of the distinct vertices `(v, *)` with `∂Λ(v) ⊆ Z`. So Li's
theorem `thm:k-graphs` (arXiv:2110.04505v2, l.2124, read at source) makes `D` of
type `F_∞`. For `g ∈ F(𝒢)`, `g x id` is locally a product of a bisection of `𝒢`
and a unit of `𝒢_(O_2)`, so it lies in `D`, and the map is injective.

**Step 2 (pieces).** No path of `Λ` joins vertices of different `Λ^(s)`, so the
sets `C''_s` are clopen and invariant, and `D = ∏_s F(𝒢''|_(C''_s))`.

**Step 3 (comparison, item 2).** Every clopen `U ⊆ C''_s` is a finite disjoint
union of cylinders. Record a decomposition by its *type vector*
`a ∈ N^(V_s)`, which counts the cylinders with each source; `V_s` is the vertex
set of `Λ^(s)`.
- **Equal vectors give equivalence.** If `U` and `W` have decompositions with the
  same type vector, pair cylinders `Z(λ), Z(λ')` with equal sources. The prefix
  replacements `λx ↦ λ'x` glue to a compact open bisection from `U` onto `W`.
- **Refinement moves.** Replacing `Z(λ)`, with `s(λ) = w`, by the cylinders
  `Z(λe)`, for `e` the colour-`j` edges with range `w`, is again a decomposition
  (unique factorization). In a colour `j <= k` the source `w` survives, because
  `w` has a colour-`j` loop, and the sources of the other edges join the support.
  In colour `k+1` the move adds exactly one cylinder with source `w`.
- **Conclusion.** `Λ^(s) x O_2` is strongly connected, so every vertex of `V_s` is
  the source of a path whose range lies in the support. Repeated moves of the
  first kind make the support all of `V_s`. Moves of the second kind then raise
  each count at will. So two nonempty clopen sets in `C''_s` have decompositions
  with a common type vector, and they are equivalent.

**Step 4 (item 3).** Let `S` be the set of nonempty proper clopen subsets of
`C''`. It is countable.
- **Faithful.** Clopen sets separate points.
- **Pairs.** For `U, W ∈ S`, record which of the four Boolean atoms of `(U, W)`
  meet which `C''_s`. Two pairs with the same record have atom pieces that are
  pairwise equivalent (Step 3). These bisections glue to one with source and range
  `C''`, which is an element of `D` carrying the first pair to the second. There
  are finitely many records, hence finitely many orbits of 2-element subsets.
- **Stabilizers.** An element preserving `U` splits into its restrictions to `U`
  and to `C'' \ U`, each in the full group. So the stabilizer is
  `F(𝒢''|_U) x F(𝒢''|_(C'' \ U))`, and `F(𝒢''|_U) = ∏_s F(𝒢''|_(U ∩ C''_s))`.
  For nonempty `U ∩ C''_s`, a bisection onto `C''_s` (Step 3) conjugates
  `F(𝒢''|_(U ∩ C''_s))` onto `F(𝒢''|_(C''_s))`. That group is a direct factor of the
  finitely presented `D`, hence finitely presented. So stabilizers are finitely
  generated.
- **Finite presentation.** `D` is finitely presented by Step 1.
So the action is of type (A).

**Step 5 (item 4).** By `type-a-action-gives-boone-higman-for-subgroups`, every
subgroup of `D` has solvable word problem and embeds in a finitely presented
simple group. So `D ∈ B_A`, and so is its subgroup `F(𝒢)` (item 1 of
`boone-higman-type-a-class-closed-under-finite-extensions`).
