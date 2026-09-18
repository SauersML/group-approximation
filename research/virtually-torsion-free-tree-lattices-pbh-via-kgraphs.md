---
rg: 2
id: virtually-torsion-free-tree-lattices-pbh-via-kgraphs
kind: route
title: Embed a torsion-free finite-index subgroup in the full group of its powered cube k-graph, split the power into strongly connected pieces, and stabilize by the Cuntz groupoid
target: virtually-torsion-free-tree-lattices-satisfy-pbh
requires: [torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups, tree-lattice-kgraph-power-phase-proof, stabilized-kgraph-full-groups-have-type-a-actions, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation as in `tree-lattice-kgraph-power-phase-proof`.

**Step 0 (reduction).** Let `Γ_0` be the factor-preserving subgroup (finite index)
and `Γ_1 ≤ Γ_0` torsion-free of finite index. Since `B_A` is closed under
finite-index overgroups (item 2 of `boone-higman-type-a-class-closed-under-finite-extensions`),
it suffices that `Γ_1 ∈ B_A`. `Γ_1` acts freely on `X`, since its vertex
stabilizers are finite and torsion-free, and with finitely many orbits. By
`torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups`, `Γ_1 ≤ F(𝒢_(Λ_N)|_Z)`,
where `Z` is the union of all vertex boundaries (each once) and `Λ_N` has at least
two loops of every colour at every vertex.

**Step 1 (Λ_N splits into strongly connected pieces).** For vertices `v, w` of
`Λ`, write `v ⇝ w` if some path of `Λ` with range `v` and source `w` has degree in
`N·N^k`. These are exactly the paths of `Λ_N`.
- `⇝` is reflexive (loops) and transitive.
- **Symmetric.** `Λ` is strongly connected (Step 3 of the phase route). Given `λ`
  from `v` to `w` of degree `Nm`, take any `μ` from `w` to `v` of degree `d`. Then
  `(μλ)^(N-1) μ` runs from `w` to `v` with degree
  `(N-1)(d + Nm) + d = Nd + N(N-1)m`, a multiple of `N`.
So `⇝` is an equivalence relation. No path of `Λ_N` joins different classes, and
`Λ_N` restricted to each class is strongly connected. Thus `Λ_N` is a disjoint
union of strongly connected finite `k`-graphs, each vertex keeping its two loops
of every colour.

**Step 2 (conclusion).** `Λ_N` and `Z` satisfy the hypotheses of
`stabilized-kgraph-full-groups-have-type-a-actions`, so `F(𝒢_(Λ_N)|_Z) ∈ B_A`. Its
subgroup `Γ_1` lies in `B_A`, and hence so does `Γ`.
