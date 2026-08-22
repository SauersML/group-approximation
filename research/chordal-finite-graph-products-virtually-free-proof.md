---
rg: 2
id: chordal-finite-graph-products-virtually-free-proof
kind: route
title: Induct along Dirac clique separators and glue finite graphs of finite groups
target: chordal-graph-products-of-finite-groups-have-lp
requires: []
artifacts:
  - research/artifacts/enders-shulman-ffw-llp-sources-2026-08-21.md
---

**(a).**  Induction on `|V(X)|` for the claim: `G_X` is the
fundamental group of a finite graph of finite groups, hence finitely
generated virtually free (Karrass--Pietrowski--Solitar / Bass--Serre:
such a group acts cocompactly on a tree with finite stabilizers).

*Base.*  `X` complete: `G_X = prod_v G_v` is finite.

*Disconnected step.*  `G_X` is the free product of the graph products
of the components: a one-edge-at-a-time free product of fundamental
groups of finite graphs of finite groups is again one (join the two
underlying graphs by an edge with trivial edge group).

*Separator step.*  `X` connected, not complete.  Pick non-adjacent
`u, w` and a minimal set `S` separating them; minimality gives every
vertex of `S` a neighbour in both sides, so if `S` contained
non-adjacent `s, t`, a shortest `s`-to-`t` path through the
`u`-component followed by one through the `w`-component would be an
induced cycle of length `>= 4` without chord, contradicting
chordality.  Hence `S` is a clique (Dirac).  Write `X = X_1 cup_S
X_2` with `X_i` the induced (chordal, proper) subgraphs on `S` plus
the two unions of components of `X - S`.  Presentations match on both
sides (von Dyck twice):

```text
G_X = G_{X_1} *_{G_S} G_{X_2},        G_S = prod_{v in S} G_v finite.
```

By induction `G_{X_i} = pi_1(Y_i)` for finite graphs of finite
groups `Y_i`.  The finite subgroup `G_S <= pi_1(Y_i)` fixes a point
of the Bass--Serre tree of `Y_i` (a finite group acting on a tree has
a fixed point), so it is conjugate into a vertex group of `Y_i`;
after conjugating, form the graph of groups `Y` = `Y_1 u Y_2` joined
by one new edge with edge group `G_S` embedded into the two chosen
vertex groups.  Then `pi_1(Y) = G_{X_1} *_{G_S} G_{X_2} = G_X`, a
finite graph of finite groups.  This proves virtual freeness; the
statement (without this proof) is Lohrey--Sénizergues 2007.

*LP.*  `G_X` finitely generated virtually free implies `C*(G_X)` has
the LP by Enders--Shulman arXiv:2403.12224 Corollary 4.6
(source-verified this date, see artifact); LP implies LLP.

**(b).**  An induced subgraph `Y c X` gives a retract subgroup
`G_Y <= G_X` (kill the generators outside `Y`; the retraction fixes
`G_Y` pointwise, so `G_Y` embeds).  For the induced square, `C_4` is
the join of the two non-edges `{1,3}` and `{2,4}`, and a graph
product over a join is the direct product of the parts:

```text
G_{C_4} = (G_1 * G_3) x (G_2 * G_4).
```

Each factor is infinite (a free product of two nontrivial finite
groups), so picking infinite-order elements `a in G_1 * G_3`,
`b in G_2 * G_4` gives `<a> x <b> = Z x Z <= G_X`.  A virtually free
group cannot contain `Z x Z`: subgroups inherit the action on a tree
with finite stabilizers, so `Z x Z` would be virtually free, but
every finite-index subgroup of `Z x Z` is again `Z x Z`, which is
abelian, non-cyclic, hence not free.  This proves non-virtual-
freeness.

If `(|G_1|-1)(|G_3|-1) >= 2`, the free product `G_1 * G_3` is not
virtually cyclic and contains `F_2` (classical: e.g. for
`|G_1| >= 2, |G_3| >= 3` take `x in G_1, y, y' in G_3` nontrivial
with `y != y'`; the commutators of `xy` and `xy'` generate a free
subgroup via the ping-pong/normal-form argument, or cite that an
amalgam of finite groups is virtually free of Euler characteristic
`1/|G_1| + 1/|G_3| - 1 < 0`, hence has a finite-index free subgroup
of rank `>= 2`).  With both diagonal conditions, `F_2 x F_2 <= G_X`.
Since the (L)LP passes to subgroups (recorded with the program's
standing citations in `llp-non-rf-kazhdan-group-is-non-hyperlinear`),
LLP of `C*(G_X)` would give LLP of `C*(F_2 x F_2)`, which is
precisely Fournier-Facio--Willett arXiv:2603.18456v2 Question 1.6
(read at source: "Does `F_2 x F_2` have the (L)LP?").
