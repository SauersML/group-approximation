---
rg: 2
id: tree-lattice-kgraph-power-phase-proof
kind: route
title: Build the cube k-graph, get loops from non-backtracking closed walks in a power, and absorb the Busemann lag modulo N into a phase coordinate
target: torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups
requires: [product-of-trees-faithful-factor-pbh-via-bass-serre-induction, tree-lattice-block-splitting-proof, li-finite-k-graph-full-groups-are-f-infinity]
---

Notation as in the target. An *oriented cube* is `c = (e_1, ..., e_k)` with `e_i`
a directed edge of `T_i` starting at `v_i`. Its *box* is `B_c = ∏ ∂T_(e_i)`, where
`T_(e)` is the half-tree ahead of `e`. Advancing in direction `j` replaces `e_j`
by a successor (an edge starting at the head of `e_j`, other than its reverse).

**Step 1 (the k-graph).** A *grid* of size `m ∈ N^k` from `c` is the family of
cubes reached by advancing `m_j` times in each direction `j` along chosen
non-backtracking rays. Grids compose by concatenation, with unique factorization
by sizes. `Γ` acts freely on oriented cubes, since it acts freely on vertices, and
has finitely many orbits on them. So the orbit category `Λ` is well defined:
composable orbits have unique representatives meeting at a common cube. It is a
finite `k`-graph with degree = size. An infinite path from `[c]` lifts uniquely to
an infinite grid from `c`, which is a point of `B_c`. So `∂Λ([c]) = B_c`.
Leaflessness gives paths of every degree from every vertex.

**Step 2 (colour components).** Fix `j` and an oriented `(k-1)`-cube `α` in the
other factors, with stabilizer `H_α`. `H_α` acts freely on the vertices of `T_j`
(a fixed vertex would give a fixed vertex of `X`), without inversions, and with
finitely many orbits (Lemma P of
`product-of-trees-faithful-factor-pbh-via-bass-serre-induction`). So `H_α \ T_j`
is a finite connected graph with all degrees at least 2 (leafless), and it is not
a cycle (`T_j` is not a line). The colour-`j` edges of `Λ` between vertices
`[(f, α)]` form its non-backtracking (Hashimoto) graph `B_α`, since `[(f, α)]`
determines the `H_α`-orbit of `f`. `B_α` is strongly connected: the Hashimoto
matrix of such a graph is irreducible (standard; for example Glover--Kempton,
not re-read). Its spectral radius is greater than 1, because non-backtracking
walks in `T_j` grow exponentially.

**Step 3 (strong connectivity of Λ).** Given oriented cubes `c` and `c'`, change
one coordinate at a time, `c → (e'_1, e_2, ...) → (e'_1, e'_2, e_3, ...) → ... → c'`.
Each change is a path of the corresponding colour, by Step 2. So `Λ` is strongly
connected.

**Step 4 (loops, item 2).** Let `p` be a common multiple of the periods of the
finitely many `B_α`. By Perron--Frobenius, the number of closed walks of length
`mp` at each vertex of each `B_α` tends to infinity with `m`. Choose `N = mp`
with at least two such walks everywhere. These are colour-`j` loops of degree
`ε_j` in `Λ_N`. `Λ_N` is a `k`-graph (unique factorization is inherited), finite,
with the same vertices and infinite paths as `Λ`.

**Step 5 (phases and the embedding, item 3).** Fix a base vertex `x_0 = (v_1, ..., v_k)`.
For `r ∈ R = {0, ..., N-1}^k`, let `C_r` be the set of oriented cubes whose `i`-th
edge points away from `v_i` and starts at distance `r_i` from it. Their boxes
partition `∂X = ∏ ∂T_i`. So `Φ(ξ, r)` = (the grid of `ξ` from its cube in `C_r`)
identifies `∂X x R` with a finite disjoint union `Y'` of vertex boundaries of
`Λ_N`, with repetitions.
- **Action.** `γ ∈ Γ` acts on `∂X x R` by `(ξ, r) ↦ (γξ, r')`, where
  `r'_i ≡ r_i - β_(γξ_i)(γ v_i, v_i) mod N` and `β` is the Busemann cocycle. This
  is a group action, because `β` is a cocycle.
- **It lies in the full group.** The grids `γ · Φ(ξ, r)` and `Φ(γξ, r')` lie in the
  same `Γ`-orbit up to a common tail. Their lag in direction `i` is
  `r'_i - r_i + β_(γξ_i)(γ v_i, v_i)`, which lies in `NZ`. Moving the common point
  along the tail makes both prefix degrees multiples of `N`. The lag is locally
  constant in `ξ`. So each `γ` acts on `Y'` by finitely many prefix replacements
  of `Λ_N`, that is, by an element of the full group of `𝒢_(Λ_N)` on `Y'`.
- **It is faithful.** An element trivial on `∂X` fixes all ends of every `T_i`,
  hence is trivial, since each `T_i` is leafless with at least three ends.
- **Removing repetitions.** For a vertex `w` used `m_w` times, fix two colour-1
  loops `ℓ ≠ ℓ'` at `w` in `Λ_N`. The cylinders `Z(ℓ'^t ℓ)`, `0 <= t < m_w`, are
  pairwise disjoint in `∂Λ_N(w)` and each is a copy of `∂Λ_N(w)`, by unique
  factorization. Transporting the copies of `∂Λ_N(w)` in `Y'` onto them by the
  prefix maps `x ↦ ℓ'^t ℓ x`, and extending by the identity, embeds `Γ` in `F`.

**Step 6 (item 4).** Li's theorem `thm:k-graphs` (TeX l.2124–2129, read at
source): for a finite higher rank graph with `# v d^(-1)(ε_j) v >= 2` for all `v`
and `j`, and `Y` a union of distinct vertex boundaries of `X = ∂Ω`, the full group
`F((I_l ⋉ X)_Y^Y)` is of type `F_∞`. The corollary after it restates this for
higher rank graphs, where `C^* = C^0`. `Λ_N` is cancellative, so Li's condition (F)
holds (l.1456). `I_l ⋉ ∂Ω` is the boundary path groupoid of a finite `k`-graph
without sources (Spielberg, as used by Li; not re-read). Apply it with `Y = Z`.
