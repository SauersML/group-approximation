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
residually finite `G`. The non-virtually-special cubulated groups that are not
residually finite (Wise, Burger--Mozes and Radu-type lattices beyond two trees) need
a different host.

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
