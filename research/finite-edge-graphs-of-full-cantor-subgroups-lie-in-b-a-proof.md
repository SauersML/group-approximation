---
rg: 2
id: finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a-proof
kind: route
title: Add the vertices along a maximal tree and then the remaining edges, conjugating each edge into place inside the full host and absorbing it by a centralizing HNN extension over a finite subgroup
target: finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a
requires:
  - finite-subgroups-of-full-cantor-groups-conjugacy-criterion
  - free-permutational-products-preserve-pbh
---

Lane proof (bh-free-10, 2026-09-18), not reviewed. Notation as in the target.
- **Edge conventions.** An edge `e` from `v` to `w` gives the relation
  `α_e(c) = ω_e(c)` if `e` is in the chosen maximal tree `𝒯`. Otherwise it gives
  `t_e α_e(c) t_e^(-1) = ω_e(c)`.
- **Presentation.** `π_1(𝒢)` is obtained from `G_(v_0)` by adjoining the vertices of `𝒯`
  one leaf at a time, each by an amalgam over a finite edge group, and then the edges
  outside `𝒯`, each by an HNN extension over a finite edge group.

## The invariant

After adding some vertices and edges we have a group `Q`, a group `L ∈ B_A`, and inclusions
`Q ≤ L` and `D ≤ L`. For every vertex `v` already added there is `λ_v ∈ L` with

```text
λ_v g λ_v^(-1) = ι_v(g)    for all g ∈ G_v ⊆ Q.                              (I)
```

**Start.** `Q = G_(v_0)`, identified with `ι_(v_0)(G_(v_0))`; `L = D`; `λ_(v_0) = 1`.

## The conjugator of an edge

Let `e` run from `v` to `w`, both already added. By hypothesis and
`finite-subgroups-of-full-cantor-groups-conjugacy-criterion` (Part 1, or Part 2 in the free
case), there is `β_e ∈ D` with

```text
β_e ι_v(α_e(c)) β_e^(-1) = ι_w(ω_e(c))    for all c ∈ C_e.
```

Put `s_e = λ_w^(-1) β_e λ_v ∈ L`. By (I),

```text
s_e α_e(c) s_e^(-1) = λ_w^(-1) ι_w(ω_e(c)) λ_w = ω_e(c).                     (C)
```

## Leaf step

Let `w` be new, joined to `v` by a tree edge `e`. The new group is
`Q' = Q *_(C_e) G_w`, amalgamated along `α_e` and `ω_e`.
- Here `λ_w` is not yet defined, so define `μ: G_w -> L` by
  `μ(g) = λ_v^(-1) β_e^(-1) ι_w(g) β_e λ_v`.
- Then `μ(ω_e(c)) = λ_v^(-1) ι_v(α_e(c)) λ_v = α_e(c)`, by the defining property of
  `β_e` and (I).
- So `Q ≤ L` and `μ(G_w) ≤ L` meet the amalgamation compatibly. By Part 4 of
  `free-permutational-products-preserve-pbh-proof`, `Q'` embeds in
  `L' = L *_(A) (A × ⟨t⟩)` with `A = α_e(C_e)`, by `q -> q` on `Q` and
  `g -> t μ(g) t^(-1)` on `G_w`. `L'` lies in `B_A` by Part 3 there, since `A` is finite.
- **Invariant.** Old vertices keep their `λ`, since `Q` embeds identically.
  - Put `λ_w = β_e λ_v t^(-1)`. Then
    `λ_w (t μ(g) t^(-1)) λ_w^(-1) = β_e λ_v μ(g) λ_v^(-1) β_e^(-1) = ι_w(g)`.
  - `D ≤ L ≤ L'`.

## Loop step

Let `e ∉ 𝒯` run from `v` to `w`. The new group is `Q' = Q*_(θ_e)` with
`θ_e = ω_e α_e^(-1)`. By (C), `θ_e` is conjugation by `s_e ∈ L`. By Part 5 of
`free-permutational-products-preserve-pbh-proof`, `Q'` embeds in
`L' = L *_(B) (B × ⟨u⟩)` with `B = ω_e(C_e)`, by `q -> q` and `t_e -> u s_e`. `L' ∈ B_A` by
Part 3 there. `Q` embeds identically, so (I) persists.

## End

After all vertices and edges, `π_1(𝒢) = Q ≤ L ∈ B_A`. `∎`

## The examples

The examples follow from the free case, using the example section of
`finite-subgroups-of-full-cantor-groups-conjugacy-criterion`: `V` is full and clopen
transitive, and finite subgroups of `T` act freely.
- `V ∈ B_A`, by BFFHZ Theorem C (finitely presented, simple, MIF), or by
  `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.
- **Not residually finite.** A residually finite group has residually finite subgroups. The
  examples contain `T`, which is infinite, simple, and hence not residually finite.
