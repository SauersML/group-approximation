---
rg: 2
id: spherical-path-upward-flagness-reduces-to-bottom-triples-proof
kind: route
title: Lower one vertex of a triple to the bottom type, bound the lowered triple, then take meets
target: spherical-path-upward-flagness-reduces-to-bottom-triples
requires:
  - huang-relative-artin-complex-structure-lemmas
---

Write `P` for the vertex poset of `Δ_Λ`, and `t(x) ∈ {1, …, n}` for the index of the type of `x`.
By structure lemmas 3, 4 and 6 (`Λ` is admissible in itself), `P` is a weakly graded bowtie-free
poset, so two elements with a common lower bound have a meet.

**Upper sets of bottom vertices.** Let `x` have type `ŝ_1`. By structure lemma 2,
`lk(x, Δ_Λ) ≅ Δ_{Λ_{>1}}`, type-preserving, since `Λ − {s_1} = Λ_{>1}` is connected. `Δ_Λ` is flag,
so adjacency inside the link is adjacency in `Δ_Λ`. Hence `V_{>x}` is order-isomorphic to the poset
of `Δ_{Λ_{>1}}`, and `V_{≥x} = {x} ∪ V_{>x}` has `x` as its minimum. By (a), `V_{≥x}` is upward flag:
a triple containing `x` is bounded by any upper bound of the other two elements.

**Induction.** Let `x_1, x_2, x_3` be pairwise upper-bounded, with `y_{12} ≥ x_1, x_2`,
`y_{23} ≥ x_2, x_3` and `y_{31} ≥ x_3, x_1`. Induct on `σ = t(x_1) + t(x_2) + t(x_3)`.

- If `σ = 3`, all three have type `ŝ_1`, and (b) applies.
- Otherwise, say `t(x_1) ≥ 2`. Every vertex lies in a chamber, which contains a type-`ŝ_1`
  vertex, so there is `x_1'` of type `ŝ_1` with `x_1' < x_1`. The triple `{x_1', x_2, x_3}` is
  pairwise upper-bounded (by `y_{12}`, `y_{23}`, `y_{31}`) and has smaller `σ`, so it has a common
  upper bound `z'`.
  - `y_{12}` and `z'` have the common lower bounds `x_2` and `x_1'`, so the meet
    `z_1 = y_{12} ∧ z'` exists and satisfies `z_1 ≥ x_2` and `z_1 ≥ x_1'`.
  - Likewise `z_3 = y_{31} ∧ z'` exists with `z_3 ≥ x_3` and `z_3 ≥ x_1'`.
  - The triple `{x_1, z_1, z_3}` lies in `V_{≥x_1'}` and is pairwise upper-bounded there: `x_1, z_1`
    by `y_{12}`, `x_1, z_3` by `y_{31}`, and `z_1, z_3` by `z'`. All three bounds are `≥ x_1'`.
  - By upward flagness of `V_{≥x_1'}` there is `z ≥ x_1, z_1, z_3`. Then `z ≥ x_2` and `z ≥ x_3`.

**Converse.** If `P` is upward flag, (b) is a special case. For (a), a pairwise upper-bounded
triple in `V_{>x}` has a common upper bound in `P`, which is `> x` and so lies in `V_{>x}`.

**For the induction along the path.** Apply the statement to `Λ_{>1}`, `Λ_{>2}`, …. The two-vertex
path `I_2(m)` with `m ≥ 4` is upward flag, because `Δ_{I_2(m)}` has girth at least 8 (structure
lemma 5).
