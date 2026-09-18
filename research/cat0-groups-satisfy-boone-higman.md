---
rg: 2
id: cat0-groups-satisfy-boone-higman
kind: claim
root: true
title: Every CAT(0) group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over every finitely generated group with solvable word problem; this only over groups acting properly and cocompactly by isometries on CAT(0) spaces, a strictly weaker open problem that the conjecture implies.
  hyperbolic-groups-satisfy-boone-higman: that covers hyperbolic inputs; this asks for all CAT(0) groups, most of which contain Euclidean planes.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that settles the subclass of lattices in products of two trees; this asks for every CAT(0) group.
  one-relator-groups-satisfy-boone-higman: that is item (9) of the same survey list; this is item (10).
---

**OPEN.** Every group acting properly and cocompactly by isometries on a CAT(0)
space embeds in a finitely presented simple group.

## Where it is asked

- **The question.** Belk--Bleak--Matucci--Zaremsky, *Progress around the
  Boone--Higman conjecture*, arXiv:2306.16356, TeX fetched on MSI 2026-09-13,
  Problem `prob:summary`: "Prove the Boone--Higman conjecture for: ... (10)
  CAT(0) groups."
- **No progress reported.** The survey's Remark `rmk:solved` records progress on
  items (1), (2), (3), (4), (8) and (13), and says nothing about (10).

## Covered subclasses (all ESTABLISHED on main)

1. **Hyperbolic CAT(0) groups:** `hyperbolic-groups-satisfy-boone-higman`.
2. **Groups virtually in a right-angled Artin group,** among them the virtually
   special cubulated groups: they are linear over `Z`. See the survey Theorem 5.1
   as recorded in `research/artifacts/boone-higman-frontier-2026-09-12.md` §5, and
   `char-zero-linear-groups-satisfy-permutational-boone-higman`.
3. **Leary--Minasyan groups:** BLIW Corollary `cor:Leary-Minasyan-groups`
   (arXiv:2408.05673 TeX l.988--990): "All Leary--Minasyan groups constructed in
   \cite{LeaMin-21} satisfy the Boone--Higman Conjecture. In particular, there
   is a CAT(0) group that is not virtually biautomatic and satisfies the
   Boone--Higman Conjecture." Now subsumed, in permutational form, by item 5.
4. **Lattices in products of two trees,** residually finite or not:
   `product-of-two-trees-lattices-satisfy-permutational-boone-higman`.
5. **Every group acting properly and cocompactly on `E^n × T`** (`T` a locally
   finite tree), in `B_A`: instance (a) of
   `cat0-groups-with-a-tree-factor-lie-in-type-a-class` (2026-09-18, lane proof).
6. **Groups on `Y × T` whose tree-vertex stabilizer `G` has a faithful member of
   `BS_G`,** in `B_A`: item 2 of the same node. This includes lattices in three
   trees whose stabilizers of vertices of one factor are commensurable with a
   definite quaternion lattice over two primes, by
   `arithmetic-nsp-lattices-have-faithful-bs-members`.

## Attempts

1. **Every known method fails on Kazhdan building lattices.** Take a cocompact
   lattice `Gamma` on an irreducible Euclidean building of dimension 2.
   - **Tree methods are void.** Titz Mite--Witzel (arXiv:2509.05054v2 l.1700)
     say "Lattices on (irreducible) Euclidean enjoy Kazhdan's property (T)",
     citing unpublished work of Oppenheim. Property (T) implies property FA
     (standard, not re-read). With FA, a cocompact action on a locally finite
     tree has a global fixed point and a finite tree, so BLIW Theorem B only
     reaches finite groups.
   - **Hyperbolic methods are void.** The building contains isometric Euclidean
     planes and is quasi-isometric to `Gamma`, so `Gamma` isn't hyperbolic.
   - **Linear methods are void for exotic buildings.** See the exotic Ã₂ node
     below.
   - **The frontier node** is `exotic-a2-lattices-satisfy-boone-higman`.
2. **Products of three or more trees.**
   - **With a faithful factor, or separating factor images.** *Established*
     (2026-09-13) as `product-of-trees-lattices-with-faithful-factor-satisfy-pbh`.
     - **Finite presentation.** The edge stabilizers are finitely presented by a
       Bass--Serre induction on the number of factors.
     - **Actor.** BLIW's rigid permutation group is a type (A) actor
       (`faithful-finite-index-graphs-of-groups-have-type-a-overgroups`).
     - **Also covered.** Lattices whose factor kernels meet trivially over a set
       of factors with finitely presented image edge stabilizers.
   - **Without such factors.** Open as
     `product-of-trees-lattices-satisfy-permutational-boone-higman`. BLIW
     Theorem C needs a faithful group in `BS_G` for `G` a vertex stabilizer,
     and that forces `G` to be residually finite.
3. **Cubulated groups that are not virtually special** and don't split as
   products of trees. Hyperplane orbits give tree actions only when the
   translates are pairwise disjoint, and the dual tree is locally finite only
   when the edge stabilizers have finite index. No general method is known.
4. **Tree factors in general** (2026-09-18, lane bh-cat0). *Works whenever the
   fibre group has a faithful Baumslag--Solitar member.*
   - For `Γ` on `Y × T`, `Γ` lies in `BS_G` for its tree-vertex stabilizer `G`
     (`cat0-groups-with-a-tree-factor-lie-in-type-a-class`, item 1).
   - One faithful member of `BS_G` puts all of `BS_G` in `B_A`
     (`bs-class-with-faithful-member-lies-in-type-a-class`).
   - Faithful members are now known for `G` virtually `Z^n`, virtually free,
     `SL_n(Z)`-commensurable (`n >= 3`) and definite-quaternion-commensurable
     (`arithmetic-nsp-lattices-have-faithful-bs-members`). The last two come from a
     commensurator element and the normal subgroup theorem.
   - **Remaining gap for this method:** fibre groups `G` that are not residually
     finite (Wise, Burger--Mozes, Radu fibres in three trees), and non-arithmetic
     residually finite `G` with the normal subgroup property but no commensurator
     element outside a finite extension of `G`.
