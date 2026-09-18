---
rg: 2
id: stabilized-kgraph-full-groups-have-type-a-actions
kind: claim
title: After stabilizing by the Cuntz groupoid, the topological full group of a loop-rich finite higher-rank graph acts on clopen sets with type (A), so the original full group lies in the type (A) class
distinct_from:
  fp-full-binary-cantor-groups-have-type-a-actions: that needs a standard binary V inside the full group, so that all clopen sets are equivalent; this gets the same equivalence from homology (every class is 0 after stabilizing) and Matui's comparison theorem, with no standard V.
  torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups: that produces the finitely presented full group; this puts such full groups in B_A.
---

**ESTABLISHED** through `stabilized-kgraph-full-group-clopen-action-proof` (lane
proof; not independently reviewed; no priority claimed). It rests on Li's
higher-rank-graph theorem (read at source) and on Matui's comparison theorem for
purely infinite minimal groupoids (cited, not re-read).

**Setting.** `Λ` is a finite `k`-graph with at least two loops of every colour at
every vertex. `Z` is the union of the boundaries of a set of distinct vertices,
and `𝒢 = 𝒢_Λ|_Z` is the reduced boundary path groupoid. Assume:
- `𝒢` is effective;
- `Z` is a finite disjoint union of clopen `𝒢`-invariant sets, on each of which
  `𝒢` is minimal.

Let `O_2` be the one-vertex 1-graph with two loops, `C'' = Z x {0,1}^N`, and
`𝒢'' = 𝒢 x 𝒢_(O_2)`, the boundary groupoid of the `(k+1)`-graph `Λ x O_2`
reduced to `C''`.

**Statement.**
1. `D = F(𝒢'')` is of type `F_∞`, and `g ↦ g x id` embeds `F(𝒢)` in `D`.
2. Every class in `H_0(𝒢'')` is zero, and `𝒢''` is purely infinite, effective and
   minimal on each of finitely many clopen invariant pieces.
3. The action of `D` on the countable set of nonempty proper clopen subsets of
   `C''` is of type (A).
4. Hence `D`, `F(𝒢)` and all their subgroups lie in `B_A`. They embed in finitely
   presented simple groups, and their finitely generated subgroups have solvable
   word problem.
