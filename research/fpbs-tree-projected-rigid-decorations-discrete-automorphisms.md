---
rg: 2
id: fpbs-tree-projected-rigid-decorations-discrete-automorphisms
kind: claim
title: Rigidly decorated tree-projected Cayley graphs of F_n x Z admit no nonunimodular fibre-preserving symmetry, and one of them has a discrete automorphism group
distinct_from:
  fpbs-tree-projected-letter-exchange-nonunimodular: that constructs a nonunimodular subgroup when two decoration sets agree up to translation and reflection; this proves that when all oriented decoration shapes are distinct, every fibre-preserving automorphism lies in a discrete group, and for one example that the whole automorphism group is discrete.
  fpbs-tree-projected-reversible-letter-nonunimodular: that constructs a nonunimodular subgroup when one decoration set is symmetric up to translation; this is the obstruction in the complementary rigid case.
  fpbs-tree-projected-cayley-graphs-strict-thresholds: that is the open root; this shows that its rigid examples are out of reach of Hutchcroft's nonunimodular theorem, so any proof there must work on unimodular graphs.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that is Hutchcroft's theorem; this shows its hypothesis fails for a Cayley graph of F_2 x Z.
artifacts:
  - research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py
  - research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma = F_n x Z` with `n >= 2`, free basis `B`, and let `S`
be a finite symmetric generating set with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)` whose vertical
part is `{(1,1),(1,-1)}`. Put `D_s = {k : (s,k) in S}` and call the decorations
*rigid* if the `2n` sets `D_s`, `-D_s` (`s in B`) are pairwise distinct up to
translation. Equivalently: no `D_s` is symmetric up to translation, and
`D_t ≠ D_s + c`, `D_t ≠ c - D_s` for distinct letters and every integer `c`.

1. **Fibre-preserving automorphisms.** If the decorations are rigid, every
   automorphism of `X = Cay(Gamma,S)` that maps each vertical line `{g} x Z` onto a
   vertical line lies in `Gamma ⋊ <alpha>`, where `alpha(g,m) = (theta(g), -m)` and
   `theta` is the automorphism of `F_n` inverting every basis letter. This group has
   vertex stabilizers of order at most 2, so it is discrete and unimodular.
2. **A graph with discrete automorphism group.** For
   `S_rig = {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}` and inverses in
   `F_2 x Z` (degree 14), vertical edges lie in exactly 4 triangles and horizontal
   edges in 0 or 2. So every automorphism is fibre-preserving, and
   `Aut(Cay(Gamma,S_rig)) = Gamma ⋊ <alpha>`.
3. **Consequence.** Every closed subgroup of `Aut(Cay(Gamma,S_rig))` is discrete,
   hence unimodular. The hypothesis of Hutchcroft arXiv:1711.02590v3 Theorem 1.2
   fails for this Cayley graph, and no lifted-tree construction exists for it. The
   status of `p_c < p_u` on it is OPEN.

**Scope.** Item 1 excludes only fibre-preserving automorphisms. Item 2 excludes all
automorphisms, but only for `S_rig`. For other rigid sets the same triangle count
often identifies the vertical edges, and then item 1 applies to the whole group.

Proof: `fpbs-rigid-decorations-discrete-automorphisms-proof`.
