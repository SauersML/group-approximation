---
rg: 2
id: artin-complex-5-3-3-11-contractible-via-b4-subdivision
kind: route
title: Haettel's criterion on the (s_4,s_5)-subdivision reduces contractibility for [5,3,3^{1,1}] to upward flagness in type H_4
target: artin-complex-of-5-3-3-11-is-contractible
requires:
  - h4-deligne-complex-upward-flag-toward-5-edge
  - d4-subdivided-artin-complex-downward-flag
  - huang-relative-artin-complex-structure-lemmas
  - haettel-flag-poset-contractibility-criterion
---

Lane w3-042, 2026-09-17; unreviewed. This is Proposition `prop:ori link0` of J. Huang,
arXiv:2405.12068, for `n = 4`, applied to a `B̃_4`-shaped diagram whose 4-edge is relabelled 5.
The inputs are that paper's Theorem `thm:downflagD4` and the `H_4` case of its Conjecture
`conj:compareB`. The argument is written out below because Huang leaves the vertex-by-vertex
reduction to the reader.

## Setting

`Λ = [5,3,3^{1,1}]` has vertices `s_1, …, s_5` with `m_{12} = 5`, `m_{23} = m_{34} = m_{35} = 3` and
all other pairs commuting. In Huang's `B̃_4` labelling, `(b_1, b_2, b_3, b_4, b_5) = (s_4, s_5, s_3, s_2, s_1)`.

Let `Δ = Δ_Λ`, a 4-dimensional simplicial complex of type `{ŝ_1, …, ŝ_5}`.

**The subdivision.** Subdivide each edge of `Δ` joining a vertex of type `ŝ_4` to a vertex of
type `ŝ_5`, and give the midpoint type `m`. Each top simplex of `Δ` has one vertex of each type.
Cut it into two top simplices along the face spanned by `m, ŝ_3, ŝ_2, ŝ_1`. Call the result `Δ'`.

Put `t = 1` on types `ŝ_4, ŝ_5`, `t = 2` on `m`, `t = 3` on `ŝ_3`, `t = 4` on `ŝ_2` and `t = 5` on `ŝ_1`.
For vertices `x, y` of `Δ'`, write `x < y` when `x, y` are adjacent in `Δ'` and `t(x) < t(y)`.

Two facts are used throughout:

- Every top simplex of `Δ'` has exactly one vertex with each value `t = 1, …, 5`.
- No two vertices with `t = 1` are adjacent in `Δ'`. Vertices of the same type are never adjacent
  in `Δ`, and the `ŝ_4 ŝ_5` edges have been subdivided.

## The four hypotheses of `haettel-flag-poset-contractibility-criterion`

**1. Simple connectivity.** `Δ'` is a subdivision of `Δ`, so it is homeomorphic to `Δ`. `Δ` is
simply connected by structure lemma 1 of `huang-relative-artin-complex-structure-lemmas`
(`|Λ| = 5 ≥ 3`).

**2. Partial order.** Only transitivity needs proof. Suppose `x < y < z`. We show that
`lk(y, Δ')` is the join of its vertices with smaller `t`, `lk_−(y)`, and its vertices with larger `t`,
`lk_+(y)`. Then `x ∗ z` is an edge of `lk(y, Δ')`. So `x, y, z` span a triangle and `x < z`.

- **`t(y) = 1`.** Then `lk_−(y)` is empty.
- **`t(y) = 2`.** `y` is the midpoint of an edge `uv` of `Δ` with `u, v` of types `ŝ_4, ŝ_5`. Its link
  in `Δ'` is `{u, v} ∗ lk(uv, Δ)`, and `lk_−(y) = {u, v}`.
- **`t(y) ≥ 3`.** Let `y` have type `ŝ_j` with `j ∈ {3, 2, 1}`. By structure lemma 2,
  `lk(y, Δ) ≅ Δ_{Λ−s_j}` preserving types. This is the join of the Artin complexes of the
  components of `Λ − s_j`, and `lk(y, Δ')` is its induced subdivision.
  - `j = 3`: the components are `{s_4}`, `{s_5}` and `{s_1, s_2}`, and the lower types are exactly
    `ŝ_4, ŝ_5`.
  - `j = 2`: the components are `{s_3, s_4, s_5}` and `{s_1}`, and the lower types are exactly
    those of the first.
  - `j = 1`: every type is lower.

  In each case `lk_−(y)` and `lk_+(y)` are unions of join factors, and subdividing inside
  `lk_−(y)` keeps the join.

The same join property also shows that for `y, z` in the link of `x`, `y < z` in `Δ'` iff `y, z`
are adjacent in `lk(x, Δ')`. So each order used below is the order of a link.

**Reduction to extreme vertices.** Let `y` be any vertex. Choose a top simplex of `Δ'` containing
`y`, and let `x'` and `x''` be its vertices with `t = 1` and `t = 5`. Then `x' ≤ y ≤ x''`, and by
transitivity `V_{≥y} ⊆ V_{≥x'}` and `V_{≤y} ⊆ V_{≤x''}`.

If a poset `P` is bowtie free and upward flag, then so is any upper set `U = P_{≥y}`:

- **Bowtie freeness.** A bowtie `x_1, x_2 < y_1, y_2` in `U` has a filler `z` in `P` with
  `z ≥ x_1 ≥ y`, so `z ∈ U`.
- **Upward flagness.** A common upper bound in `P` of elements of `U` lies in `U`.

Dually, lower sets inherit bowtie freeness and downward flagness. So it suffices to check
hypothesis 3 at vertices with `t = 1` and hypothesis 4 at vertices with `t = 5`.

Adding a minimum (resp. maximum) to a poset preserves bowtie freeness and upward (resp.
downward) flagness:

- a bowtie through the new minimum is filled by its other lower vertex;
- a triple containing the minimum is bounded by any upper bound of the other two.

**3. Upper sets at `t = 1`.** Let `x` have type `ŝ_4`; the case `ŝ_5` is symmetric under
`s_4 ↔ s_5`. Every neighbour of `x` in `Δ'` has `t ≥ 2`, so `V_{>x}` is the vertex set of
`lk(x, Δ')`.

- The top simplices of `Δ'` containing `x` are the halves `{x, m, ŝ_3, ŝ_2, ŝ_1}` of the top
  simplices of `Δ` containing `x`.
- Hence `lk(x, Δ') ≅ lk(x, Δ)`, sending the midpoint of `xv` to `v` for `v` of type `ŝ_5` and
  fixing the other vertices.
- By structure lemma 2, `lk(x, Δ) ≅ Δ_{Λ−s_4}`, the Artin complex of the path
  `s_5 −3− s_3 −3− s_2 −5− s_1` of type `H_4`.
- Under these isomorphisms, `t = 2, 3, 4, 5` corresponds to `ŝ_5 < ŝ_3 < ŝ_2 < ŝ_1`, the path order
  running toward the 5-edge.

This poset is:

- bowtie free by structure lemma 4;
- upward flag by `h4-deligne-complex-upward-flag-toward-5-edge`, with `(s_5, s_3, s_2, s_1)` in the
  roles of `(s_1, s_2, s_3, s_4)` there.

Adding the minimum `x` gives hypothesis 3.

**4. Lower sets at `t = 5`.** Let `x` have type `ŝ_1`. Every neighbour has `t ≤ 4`, so `V_{<x}` is
the vertex set of `lk(x, Δ')`.

- By structure lemma 2, `lk(x, Δ) ≅ Δ_{Λ−s_1}`, the Artin complex of type `D_4`. Its centre is
  `s_3` and its leaves are `s_2, s_4, s_5`.
- `lk(x, Δ')` is the subdivision of this complex along the leaf types `ŝ_4, ŝ_5`: its `ŝ_4 ŝ_5`
  edges are subdivided and its top simplices are cut.
- Its values `t = 1, 2, 3, 4` are the types `{ŝ_4, ŝ_5}, m, ŝ_3, ŝ_2`. This is exactly the order of
  `d4-subdivided-artin-complex-downward-flag`, with `(a, b, d, c) = (s_4, s_5, s_3, s_2)`.

So `V_{<x}` is bowtie free and downward flag, and adding the maximum `x` gives hypothesis 4.

**Conclusion.** By `haettel-flag-poset-contractibility-criterion`, `Δ'` is contractible. Hence
`Δ ≅ Δ'` is contractible.

## Converse: what this method needs

Hypotheses 1, 2 and 4 hold unconditionally. Hypothesis 3 holds for `Δ'` **if and only if** the
`H_4` complex ordered toward its 5-edge is upward flag:

- The converse direction holds at any vertex `x` of type `ŝ_4`. There, `V_{>x}` is
  order-isomorphic to the whole `H_4` poset.
- Three pairwise upper-bounded elements of `V_{>x}` have, by hypothesis 3, a common upper bound
  `u ∈ V_{≥x}`.
- `u ≠ x`, since `u` lies above elements that are `> x`.

So the subdivision route for `[5,3,3^{1,1}]` is *equivalent* to
`h4-deligne-complex-upward-flag-toward-5-edge`. It is not a weaker substitute.

The path-order route `artin-complexes-4335-5335-contractible-via-haettel-criterion` has the same
feature: its hypothesis 3 at a vertex of type `ŝ_1` is again this `H_4` statement.

Thus three of the four compact hyperbolic 4-simplex groups, `[4,3,3,5]`, `[5,3,3,5]` and
`[5,3,3^{1,1}]`, satisfy the K(π,1) conjecture as soon as this single statement about the
spherical Artin group `A_{H_4}` holds. This is by `artin-k-pi-1-from-contractible-artin-complex`,
since `Λ` is almost spherical.

Whether contractibility of `Δ_Λ` implies `H_4` upward flagness is not known. The converse above
concerns only the criterion.
