---
rg: 2
id: virtually-torsion-free-cubulated-groups-satisfy-boone-higman
kind: claim
title: Every virtually torsion-free cubulated group embeds in a finitely presented simple group (Belk--Bleak--Chatterji--Matucci--Perego, Question 1.15)
distinct_from:
  cat0-groups-satisfy-boone-higman: that is BBMZ Problem 5.3(10) for all CAT(0) groups; this is the cubical subclass, asked separately by BBCMP.
  cubulated-hyperbolic-groups-are-virtually-special: that settles the hyperbolic cubulated case via Agol; this asks for all cubulated groups, most of which contain flats.
---

**OPEN.**

**Where it is asked.** Belk--Bleak--Chatterji--Matucci--Perego, *Rational embeddings
of continuous automatic groups* (preliminary preprint, author's page; copy in the
swarm source store `src/bbcmp/`), p. 7: "Finally, recall that a group G is
cubulated if it acts geometrically (i.e. properly and cocompactly by isometries) on
a CAT(0) cube complex." and "Question 1.15. Does every virtually torsion-free
cubulated group admit an embedding into a finitely presented simple group?" They
prove (Theorem 1.13) that such groups are continuous automatic and embed in the
rational group, and note it is unknown whether the topological full group of the
Roller boundary action is finitely presented.

**Known cases (on main).**
1. Virtually special cubulated groups: linear over `Z`, hence in an f.p. simple
   group (`char-zero-linear-groups-satisfy-permutational-boone-higman`); they also
   embed in RAAGs, which embed in Brin--Thompson groups.
2. Hyperbolic cubulated groups: virtually special by Agol
   (`cubulated-hyperbolic-groups-are-virtually-special`).
3. Lattices in products of two trees, residually finite or not
   (`product-of-two-trees-lattices-satisfy-permutational-boone-higman`).
3 bis. **Every cocompact lattice on a finite product of thick leafless trees**, any
   number of factors, torsion allowed, residually finite or not:
   `cocompact-tree-product-lattices-lie-in-type-a-class` (bh-lattices, 2026-09-18,
   lane proof). The host is the full group of the cube `k`-graph of the lattice
   (`tree-lattice-kgraph-power-phase-proof`,
   `stabilized-kgraph-full-groups-have-type-a-actions`,
   `tree-lattice-with-torsion-via-zappa-szep-kgraphs`). This covers the Wise,
   Burger--Mozes and Radu lattices and their higher-dimensional analogues.
4. Groups acting geometrically on `E^n × T`, `H^2 × T`, or `X × T` with arithmetic
   fibres, when cubulated (`cat0-groups-satisfy-boone-higman`, covered items 5--8).
5. **New:** groups acting geometrically on `Y × T` (`Y` a locally finite CAT(0) cube
   complex) whose `Y`-projection has a closure satisfying (FB):
   `cube-complex-times-tree-lattices-with-fb-closures-are-pbh`.
6. **New:** every torsion-free group `G` acting geometrically on a locally finite
   CAT(0) cube complex `X` such that finitely many elements of `Comm_(Aut X)(G)`
   generate, together with `G`, a subgroup whose closure satisfies (FB). This is
   item 3 of `cubical-hecke-members-faithful-when-closure-fixes-bounded-sets`.

**What the new criterion cannot do.** By item 4 of that node, it only ever reaches
residually finite `G`. The non-residually-finite lattices on products of trees are
covered instead by item 3 bis. What remains open is the cubulated groups whose cube
complex is not a product of trees (up to the group action) and which are neither
virtually special nor covered by items 4--6.

## Attempts

1. **(bh-free-36, 09-18) Hyperplane-orbit tree actions.** A `G`-invariant colouring
   of hyperplanes with no crossings inside a colour class embeds `X` in a product of
   dual trees `∏ T_c`. `G` then acts on each `T_c` cocompactly, but the dual trees
   are usually not locally finite and the diagonal action is not proper off the
   image of `X`. So neither BLIW Theorem B nor the product-of-trees results apply.
   The obstruction to type (A) actions on hyperplanes themselves is that the
   combinatorial distance between hyperplanes is a `G`-invariant of pairs with
   unbounded values, so there are infinitely many orbits on pairs.
2. **(bh-free-36, 09-18) Commensurator route.** The t.d.l.c. criterion above,
   producing `G ∈ B_A` from a large commensurator closure. It is void for
   commensurator-rigid and for non-residually-finite `G`.
3. **(bh-free-36, 09-18) Rank-one recoding of Niblo--Reeves normal forms fails on
   products of trees.** `prefix-replacement-actions-recode-into-germ-extensions-of-v`
   needs each generator to act by state-preserving prefix replacements off finitely
   many points. Take `X = T_1 × T_2` (thick trees) with the Niblo--Reeves coding of
   `∂T_1 × ∂T_2` by sequences of squares from the base vertex `(o_1, o_2)`, and `γ`
   hyperbolic on `T_1` with translation length `ℓ > 0` and fixing `o_2`. Such `γ`
   exist in every cocompact lattice: the stabilizer of `o_2` acts cocompactly on
   `T_1`.
   - The Busemann functions `β_i(γ, ·)` (based at `o_i`) are locally constant on
     `∂T_i`, so `U = {(ξ_1, ξ_2) : β_1(γ, ξ_1) ≠ β_2(γ, ξ_2)}` is clopen. Here
     `β_2 ≡ 0` because `γ` fixes `o_2`, and `β_1 = ±ℓ` on a neighbourhood of the
     attracting end `γ^+`, so `U` contains `N × ∂T_2` for that neighbourhood `N`.
   - On `U`, `γ` shifts the `T_1`-index of the square sequence by `β_1` and the
     `T_2`-index by `β_2`. A prefix replacement `λz ↦ μz` shifts both by one common
     amount. If `γ` agreed with `λz ↦ μz` on a cylinder inside `U`, it would do so
     at a point of that cylinder whose two coordinate tails are not eventually
     periodic, which is impossible. So `γ` is singular at every point of `U`.
   - So the singular set is uncountable and the recoding theorem does not apply. The
     obstruction is the rank of the flats, not the choice of coding within rank one;
     the working host is the rank-`k` full group of item 3 bis.
   - For a general cubulated group the same step fails wherever the Roller boundary
     contains a product of two Cantor sets on which one element has mismatched
     Busemann rates. A Garside-category coding in the sense of X. Li
     (arXiv:2110.04505), with a power-and-phase trick as in item 3 bis, is the
     natural replacement. Whether Niblo--Reeves normal cube paths give such a finite
     Garside coding is exactly BBCMP's remark that finite presentation of the
     Roller-boundary full group is unknown.
