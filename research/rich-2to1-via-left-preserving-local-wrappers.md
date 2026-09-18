---
rg: 2
id: rich-2to1-via-left-preserving-local-wrappers
kind: route
title: Dead -- keep the left labels of a proved 2-to-1 instance and add locally complete right vertices over affine intended classes until the matchings are rich
target: rich-2to1-games-conjecture
requires: []
---

**Dead.** The attack starts from hard 2-to-1 instances, such as Grassmann
incidence games with affine intended labels. It keeps their left vertices and
alphabets. It then compresses, merges or adds right vertices whose 2-to-1
constraints are locally complete over the affine local intended classes. The aim
is for the matchings seen at every left vertex to become uniform, or at least
pair-uniform, while the NO case stays sound.

It is killed by `left-preserving-local-richness-wrappers-are-affine-ug-merges`:

* Local completeness forces each right vertex to absorb its agreement subgroup.
  So the vertex either carries only translation (`F_lin`) pairings or is a right
  merge of an affine unique-game clique.
* Pair-uniformity leaves translations at most `alpha_k = (4k-5)/((2k-1)(2k-3))`
  of the mass.
* The output value is then at least `(1 - alpha_k)` times the value of an
  explicit affine unique game `U_W(G)` on the same left vertices. With certified
  completeness, `G -> U_W(G)` is already a UG hardness reduction.

So the route proves rich 2-to-1 hardness only where UGC is already available on
its input. Composing 2-to-1 maps separately gives 4-to-1 constraints (recorded
under `smooth-design-rich-2to1-hardness`).

What survives, per the claim, is gaps (G1)-(G4):

* re-encoded left labels, as in long-code composition;
* completeness without local certificates;
* non-affine intended classes;
* richness on only part of the left mass.
