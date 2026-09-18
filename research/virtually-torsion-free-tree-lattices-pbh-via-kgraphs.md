---
rg: 2
id: virtually-torsion-free-tree-lattices-pbh-via-kgraphs
kind: route
title: Embed a torsion-free finite-index subgroup in the full group of its powered cube k-graph, check effectiveness and minimal pieces, and stabilize by the Cuntz groupoid
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
where `Z` is the whole unit space `∂Λ` (all vertex boundaries, each once) and
`Λ_N` has at least two loops of every colour at every vertex.

**Step 1 (𝒢_Λ is effective).** For `x ∈ ∂Λ([c])`, corresponding to `ξ ∈ B_c`, a
nontrivial isotropy element is `(x, m - n, x)` with `m ≠ n` and
`σ^m x = σ^n x`. Lifting to `X`, some `γ ∈ Γ_1` fixes `ξ` and translates along
the ray to `ξ_j` for some `j` with `m_j ≠ n_j`, so `pr_j(γ)` is hyperbolic with
`ξ_j` an end of its axis. For each `j`, the ends of axes of hyperbolic elements
of `pr_j(Γ_1)` form a countable set. `∂T_j` has no isolated points. So points `ξ`
avoiding these sets in every coordinate are dense in every box, and they have
trivial isotropy. A second countable étale groupoid with dense trivial isotropy
is effective. `𝒢_(Λ_N)` is an open subgroupoid of `𝒢_Λ` with the same unit space,
so it is effective too.

**Step 2 (𝒢_Λ is minimal).** `Λ` is strongly connected (Step 3 of the phase
route). For `x ∈ ∂Λ` and a path `λ`, choose `n`, and a path `μ` from `s(λ)` to
the range of `σ^n x`. Then `λ μ σ^n x ∈ Z(λ)` is tail equivalent to `x`. So every
orbit is dense.

**Step 3 (finitely many minimal pieces for Λ_N).** `𝒢_(Λ_N)` is the kernel of the
continuous cocycle `c = d mod N : 𝒢_Λ -> A = (Z/N)^k`. Let `𝒢_Λ ⋊_c A` be the
skew product on `∂Λ x A`.
- Choose a minimal closed invariant set `M` (by compactness). Its translates
  `a + M` are minimal, and `M` projects onto `∂Λ` (the projection of an orbit is a
  `𝒢_Λ`-orbit, which is dense by Step 2). So the translates cover `∂Λ x A`.
- Two minimal sets are equal or disjoint, so `∂Λ x A` is a finite disjoint union
  of closed minimal invariant sets, and each is clopen.
- The `𝒢_(Λ_N)`-orbit of `y` is the skew orbit of `(y, 0)` intersected with the
  clopen set `∂Λ x {0}`. So the sets `(a + M) ∩ (∂Λ x {0})` are finitely many clopen
  `𝒢_(Λ_N)`-invariant pieces of `Z`, each minimal.

**Step 4 (conclusion).** By Steps 0–3, `Λ_N` and `Z` satisfy the hypotheses of
`stabilized-kgraph-full-groups-have-type-a-actions`, so `F(𝒢_(Λ_N)|_Z) ∈ B_A`.
Its subgroup `Γ_1` lies in `B_A`, and hence so does `Γ`.
