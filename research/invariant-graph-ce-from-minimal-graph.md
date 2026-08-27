---
rg: 2
id: invariant-graph-ce-from-minimal-graph
kind: route
title: The minimal graph is a legal witness for the existential
target: invariant-graph-crossed-product-ce
requires: [minimal-marked-graph-crossed-product-ce, minimal-marked-graph-nondegenerate]
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

## Why sufficient

`invariant-graph-crossed-product-ce` asks for **some** `G`-invariant graph
`S` on `X = G/Γ` with `{o,y} ∈ S`, `b_S` nondegenerate, and `A_S ⋊ G` Connes
embeddable.  Take `S = S_min`, the orbital graph of the marked double coset
`ΓhΓ`.

* `{o,y} ∈ S_min` by construction — `S_min` is the `G`-orbit of the marked
  pair, the smallest invariant graph containing it.
* `b_{S_min}` is nondegenerate: the second prerequisite.
* `A_{S_min} ⋊ G` is Connes embeddable: the first prerequisite.

So the existential is witnessed, and the route is the trivial one.  Its point
is bookkeeping in the right direction: before
`minimal-marked-graph-nondegenerate` the target's own body flagged the
minimal member's nondegeneracy as an open sub-question, so the cheapest
candidate could not be used and the algebraic half of that claim was still a
search over graphs.  It no longer is: the search collapses to one named
algebra, and the residue is the single analytic hole
`minimal-marked-graph-crossed-product-ce`.

The reduction runs one way only.  A different member of the family — the
complete graph of `kun-thom-clifford-crossed-product-ce`, or anything between
— could conceivably be embeddable while the minimal one is not, so failure of
the prerequisite would not refute the target.
