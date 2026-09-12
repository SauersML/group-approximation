---
rg: 2
id: fa-subgroups-of-graph-towers-lie-in-base-pieces
kind: claim
title: Every subgroup with property FA of a finite HNN and amalgam tower is conjugate into a base group
distinct_from:
  normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree: that rules out a normal Kazhdan subgroup of a tree action with amenable edge groups; this places any subgroup with property FA, normal or not, inside a conjugate of a base group of an iterated tower, with no restriction on edge groups.
  property-t-implies-property-fa: that is the implication from property (T) to property FA, used for the consequence below; this is the fixed-point consequence of FA for iterated Bass-Serre towers.
---

Call `K` a **graph tower** over base groups `B_1,...,B_r` if there is a finite
sequence `K_1,...,K_n = K` in which each `K_j` is one of the `B_i`, an HNN
extension of some `K_i` with `i < j`, or an amalgamated free product
`K_i *_C K_l` with `i, l < j`. Vertex groups embed at each step, so each `B_i`
is a subgroup of `K`.

If `L <= K` has Serre's property FA, then `L` is conjugate in `K` into some
`B_i`.

## Consequence for step-by-step Boone--Higman upgrades

Take an input `G` with property FA, for instance an infinite finitely generated
Kazhdan group with solvable word problem (property FA by
`property-t-implies-property-fa`). Any tower containing `G` contains a
conjugate of `G` inside a base group, so the tower contributes nothing for such
inputs. A permanence argument along towers settles an FA input only if a base
group already contains it. In particular the premise
`decidable-groups-embed-in-decidable-edge-towers` contains Boone--Higman for
all decidable FA inputs as a special case.
