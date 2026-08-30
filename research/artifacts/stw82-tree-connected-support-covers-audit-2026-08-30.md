---
rg: 2
title: STW LXXXII finite-tree componentwise support-cover audit (2026-08-30)
kind: artifact
---

# Optimal componentwise covers over a finite tree

The previous connected-support theorem extends to arbitrary cozero supports
when the common algebra `C(T)` centralizes the outgoing ranges.  Fix a
tolerance `epsilon`.  Only finitely many connected components of
`U_v={h_v>0}` meet `{h_v>=epsilon}`: components are open in a finite tree and
cover that compact upper spectral set.  For each retained component `W`, the
set `{h_v>=epsilon} intersect W` is compactly contained in `W`.  Urysohn's
lemma gives a positive cutter equal to one there and supported inside `W`.
All omitted points carry `h_v<epsilon`.

The retained component family is finite and consists of connected subtrees.
Its intersection graph is chordal in the exact self-contained form needed:
replace each open component by a compact subtree with the same finite
intersection graph, root the ambient tree, and repeatedly remove the subtree
whose nearest point to the root is farthest away.  Every neighbour contains
that nearest point, so each removed vertex is simplicial.  Reverse greedy
colouring uses at most the maximum pointwise number `m` of original supports.
At a point there cannot be two components of the same original support, so
passing to components does not increase depth.

Aggregate the component cutters by original map and graph colour.  Same-label
cutters belonging to distinct maps are orthogonal, while the cutters for one
map sum to a contraction which acts as the identity wherever its support is at
least `epsilon`.  Since `C(T)` centralizes all outgoing ranges, multiplication
by these cutters preserves order zero exactly.  The original maps are
therefore split and regrouped into `m` colours with error below `epsilon`.
The theorem assumes the original direct-sum outgoing map is c.p.c., or
equivalently `sum_v h_v<=1`; because the cutters for each `v` sum to at most
one, this same inequality keeps the regrouped outgoing map contractive.

# Why this is a genuine recolouring theorem

The global overlap graph of the unsplit supports can require more than `m`
colours.  On an interval take three disjoint bump functions `a,b,c` and the
supports

```text
h_1=(a+c)/2,    h_2=(a+b)/2,    h_3=(b+c)/2.
```

Their overlap graph is `K_3`, but only two are active at any point.  Splitting
over the six cozero components gives an exact two-colour incidence pattern.
Thus the theorem beats `stw82-indivisible-order-zero-reuse-is-graph-colouring`
rather than merely computing its chromatic number.

It also improves the general finite-dimensional central-spectrum theorem.  A
one-dimensional spectrum there costs `2m` colours; a finite tree now costs
only `m`, without connectedness of individual supports.  This is a structural
outgoing-colour reorganization, not a new estimate on raw complementary cuts.

# Commutation and extension boundary

For arbitrary disconnected supports, the Urysohn cutters are elements of the
common `C(T)` and need not be functions of one unit support.  The new clause
therefore assumes that this common algebra centralizes every outgoing range.
The old connected-support theorem remains as a second clause with no common-
centralizer assumption: one cutter `g(h_v)` per map is enough, and it commutes
by order-zero functional calculus.

For extension gluing, it is enough to construct endpoint approximations whose
outgoing supports lie in a common centralizing finite-tree algebra and have
pointwise depth at most the endpoint maximum plus one.  No assertion is made
that an arbitrary stable essential extension admits such approximations.
