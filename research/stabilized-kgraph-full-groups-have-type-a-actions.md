---
rg: 2
id: stabilized-kgraph-full-groups-have-type-a-actions
kind: claim
title: After stabilizing by the Cuntz groupoid, the topological full group of a loop-rich finite higher-rank graph acts on clopen sets with type (A), so the original full group lies in the type (A) class
distinct_from:
  fp-full-binary-cantor-groups-have-type-a-actions: that needs a standard binary V inside the full group, so that all clopen sets are equivalent; this proves the same equivalence combinatorially, by refining cylinder decompositions, with no standard V.
  torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups: that produces the finitely presented full group; this puts such full groups in B_A.
  primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple: that embeds full groups of primitive aperiodic 2-graphs in infinite simple groups of type F_infinity; this puts full groups of loop-rich k-graphs of any rank, disjoint unions of strongly connected pieces, into the permutational class B_A, by a comparison lemma instead of simplicity.
---

**ESTABLISHED** through `stabilized-kgraph-full-group-clopen-action-proof` (lane
proof, elementary apart from Li's theorem, which was read at source; not
independently reviewed; no priority claimed).

**Setting.** `Λ` is a finite `k`-graph that is a disjoint union of strongly
connected `k`-graphs `Λ^(1), ..., Λ^(q)`, with at least two loops of every colour
at every vertex. `Z` is the union of the boundaries of a set of distinct
vertices, and `𝒢 = 𝒢_Λ|_Z`. Let `O_2` be the one-vertex 1-graph with two loops,
`C'' = Z x {0,1}^N`, and `𝒢''` the boundary groupoid of the `(k+1)`-graph
`Λ x O_2` reduced to `C''`, which is `𝒢 x 𝒢_(O_2)`.

**Statement.**
1. `D = F(𝒢'')` is of type `F_∞`, and `g ↦ g x id` embeds `F(𝒢)` in `D`.
2. **Comparison.** `C''` is the disjoint union of the clopen invariant sets
   `C''_s = (Z ∩ ∂Λ^(s)) x {0,1}^N`. Any two nonempty clopen subsets of the same
   `C''_s` are carried onto each other by a compact open bisection of `𝒢''`.
3. The action of `D` on the countable set of nonempty proper clopen subsets of
   `C''` is of type (A).
4. Hence `D`, `F(𝒢)` and all their subgroups lie in `B_A`. They embed in finitely
   presented simple groups, and their finitely generated subgroups have solvable
   word problem.

**Correction note (same day).** The first version cited Matui's comparison
theorem for purely infinite minimal groupoids. Matui's paper (arXiv:1210.5800,
Theorem `Hopf`, read at source) proves comparison only for shifts of finite type.
Item 2 is now proved directly, and effectiveness and pure infiniteness are no
longer used.
