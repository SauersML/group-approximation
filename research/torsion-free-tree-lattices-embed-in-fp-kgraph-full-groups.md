---
rg: 2
id: torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups
kind: claim
title: A torsion-free cocompact lattice on a product of thick leafless trees embeds in the topological full group of a finite higher-rank graph with two loops of every colour at every vertex, which is of type F_infinity
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that applies Li's higher-rank-graph theorem to one explicit one-vertex 2-graph; this builds a k-graph from any torsion-free tree-product lattice and forces Li's loop hypothesis by a power-and-phase trick.
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that needs a faithful or separating factor; this uses the boundary action on the product of the tree boundaries and needs no hypothesis on kernels, closures or residual finiteness.
---

**ESTABLISHED** through `tree-lattice-kgraph-power-phase-proof` (lane proof; not
independently reviewed; no priority claimed). The finiteness input is Li's
theorem for higher rank graphs, read at source (see the route).

**Setting.** `X = T_1 x ... x T_k`, `k >= 1`. Each `T_i` is locally finite and
leafless, with more than two ends. `Γ <= Aut(T_1) x ... x Aut(T_k)` is discrete
and torsion-free, with finitely many vertex orbits on `X`. So `Γ` acts freely on
`X`.

**Statement.**
1. **Cube k-graph.** The `Γ`-orbits of finite rectangular grids of oriented
   `k`-cubes of `X` form a finite `k`-graph `Λ = Λ(Γ)`. It is strongly connected,
   and for every vertex `[c]` the boundary `∂Λ([c])` is the box
   `∂T_(e_1) x ... x ∂T_(e_k)` of the cube `c = (e_1, ..., e_k)`.
2. **Loops.** For some `N >= 1`, the power `Λ_N` (paths of degree in `N·N^k`)
   has at least two loops of every colour at every vertex.
3. **Embedding.** Let `Z` be the union of the boundaries of all vertices of
   `Λ_N`, and `F = F(𝒢_(Λ_N)|_Z)` the topological full group of the boundary
   path groupoid reduced to `Z`. Then `Γ` embeds in `F`.
4. **Finiteness.** `F` is of type `F_∞`, by Li, *Left regular representations of
   Garside categories II*, arXiv:2110.04505v2, Theorem `thm:k-graphs` and the
   corollary after it.

**Scope.**
- Residual finiteness, irreducibility and the factor closures play no role. This
  includes the torsion-free Burger--Mozes and Wise lattices, and any torsion-free
  three-tree lattice left open by
  `three-tree-lattices-escape-only-via-discrete-normal-subgroups`.
- Lattices with torsion are not covered: the cube k-graph needs a free action on
  oriented cubes. A version with a finite groupoid of cube stabilizers would need
  Li's Zappa--Sz\'ep case and his condition (F).
- The embedding into a finitely presented simple group is
  `virtually-torsion-free-tree-lattices-satisfy-pbh`.
