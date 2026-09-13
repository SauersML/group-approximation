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
   Boone--Higman Conjecture." No node imports this corollary yet.
4. **Lattices in products of two trees,** residually finite or not:
   `product-of-two-trees-lattices-satisfy-permutational-boone-higman`.

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
   - **With a faithful factor.** When the action on one factor is faithful, BLIW
     Theorem B applies once the edge stabilizers are finitely presented. They are
     cocompact lattices in products of the remaining trees, hence CAT(0) groups,
     and `asymptotically-cat0-groups-have-contractible-rips` gives them a
     contractible Rips complex. The step from there to finite presentation isn't
     written on main.
   - **Without a faithful factor.** BLIW Theorem C needs a faithful group in
     `BS_G` for `G` a vertex stabilizer, and that forces `G` to be residually
     finite.
3. **Cubulated groups that are not virtually special** and don't split as
   products of trees. Hyperplane orbits give tree actions only when the
   translates are pairwise disjoint, and the dual tree is locally finite only
   when the edge stabilizers have finite index. No general method is known.
