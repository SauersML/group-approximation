---
rg: 2
id: finite-graphs-of-amenable-groups-have-sigma1-locus
kind: claim
title: Finite graph-of-groups switches over amenable vertices have a Sigma-zero-one amenable locus
distinct_from:
  genuine-hnn-switches-over-amenable-bases-are-sigma1: that treats one loop edge; this treats arbitrary finite graphs, including amalgams and the exceptional index-two line action.
  finitely-generated-centralizer-switches-are-sigma1: that treats a special one-edge centralizer construction; this closes every finite Bass-Serre assembly with finitely generated edge groups over the amenable simulators.
  amenability-of-finite-presentations-is-pi2-complete: that is the open hardness root; this proves that no finite graph-of-groups switch of the stated kind can encode totality.
---

Let `e |-> G_e` be a computable family of finite connected graphs of groups.
Assume:

- every vertex group is supplied by a finite presentation and is amenable;
- every edge group is given by a finite generating tuple;
- the two boundary maps are supplied as injective homomorphisms by words in
  the adjacent vertex generators.

Then the fundamental group is amenable exactly when a finite sequence of
standard collapses of non-loop edges with a surjective boundary map reduces
the graph of groups to one of the following elementary forms:

1. one amenable vertex and no edge;
2. one vertex and one loop for which at least one boundary map is onto, hence
   an ascending HNN extension;
3. two vertices joined by one edge whose image has index at most two at each
   endpoint, hence an amenable extension by a subgroup of the infinite
   dihedral group.

In every other case the fundamental group contains `F_2`.

Surjectivity of a finitely generated edge image onto a finitely presented
vertex group is a `Sigma^0_1` condition. So is index at most two: a
certificate supplies a second coset representative, verifies that it
normalizes the edge image and has square in it, and writes every vertex
generator in one of the two cosets. Since the graph is finite, the collapse
sequence and final-form certificate are finite. Consequently

```text
{e:pi_1(G_e) is amenable}
```

is `Sigma^0_1`.

Thus no uniform compiler assembled from finitely many amenable vertex
simulators and finitely generated Bass--Serre edges can many-one encode
`TOT`. A successful proof of amenability `Pi^0_2)-hardness for finite
presentations must leave this entire finite graph-of-groups class.

DERIVATION
[[finite-amenable-graphs-sigma1-proof]]
