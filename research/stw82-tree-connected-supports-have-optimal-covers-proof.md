---
rg: 2
id: stw82-tree-connected-supports-have-optimal-covers-proof
kind: route
title: Retain the large cozero components, colour their subtree graph, and regroup
target: stw82-tree-connected-supports-have-optimal-covers
requires:
  - stw82-order-zero-direct-sum-support-criterion
---

Fix `epsilon>0` and write `U_v={t:h_v(t)>0}`.  An R-tree is locally path
connected, so every connected component of the open set `U_v` is open.
Consider only components `W` for which

```text
K_(v,W)={t in W:h_v(t)>=epsilon}
```

is nonempty.  There are only finitely many: the components of `U_v` form an
open cover of the compact set `{h_v>=epsilon}`, so a finite subcover contains
every component meeting that set.  Moreover `W` is relatively clopen in
`U_v`, while `{h_v>=epsilon}` is a compact subset of `U_v`; hence `K_(v,W)`
is compact and contained in the open set `W`.

Normality of `T` gives a positive contraction `d_(v,W) in C(T)` such that

```text
d_(v,W)=1 on K_(v,W),       supp(d_(v,W)) subset W.    (P1)
```

The finitely many retained `W` are connected open subtrees.  Form their
intersection graph `G`.  We show that `G` is `m`-colourable.

For every edge choose a point in the intersection of its two components.
Inside each component `W`, take the geodesic convex hull of its finitely many
incident chosen points; for an isolated vertex take any singleton in `W`.
Connected subsets of an R-tree contain the unique geodesic between any two of
their points.  A finite convex hull is a finite union of compact geodesic
segments, so the resulting compact convex subtree `L_W` stays inside `W`.
The finite family `(L_W)` has exactly the graph `G` as its intersection graph.

Root `T` at a point `o`.  Metric projection onto a nonempty compact convex
subtree of an R-tree exists and is unique.  Let `a_W` be the projection of
`o` onto `L_W`, and choose `W` for which `d(o,a_W)` is maximal.  If `L_Z`
meets `L_W` at `z`, both projections lie on the geodesic `[o,z]`, and
maximality gives

```text
a_W in [a_Z,z] subset L_Z.
```

Thus all neighbours of `W` contain `a_W` and form a clique.  At a point of
`T`, at most one component belonging to a fixed original `v` can occur, and
every component containing that point lies in `U_v`.  Therefore every clique
has size at most the pointwise multiplicity `m` from (T1).  Repeated removal
of the displayed simplicial vertex, followed by reverse greedy colouring,
gives a proper colouring

```text
k(W) in {1,...,m}.                                     (P2)
```

For each original `v` and label `k`, set

```text
c_(v,k)=sum_(W component of U_v: k(W)=k) d_(v,W),       (P3)
```

where the sum runs only over retained components.  Distinct components of
one `U_v` are disjoint, so all the summands in (P3) are orthogonal and
`sum_k c_(v,k)<=1`.  If `h_v(t)>=epsilon`, then `t` lies in one retained
component and its cutter equals one at `t`; otherwise `h_v(t)<epsilon`.
Consequently

```text
norm((1-sum_k c_(v,k))h_v)<epsilon.                    (P4)
```

A proper colouring in (P2), together with the support containment in (P1),
gives `c_(v,k)c_(w,k)=0` for `v!=w`.

The common-centralizer hypothesis makes multiplication by `c_(v,k)` preserve
complete positivity and order zero.  The norm of the omitted positive map is
the norm of its value at the unit, so (P4) gives the asserted approximation.
For fixed `k`, the unit supports `c_(v,k)h_v` are orthogonal, and the
order-zero direct-sum support criterion merges them into one c.p.c.
order-zero map.

For optimality, choose `t` at which (T1) is attained and put

```text
gamma=min_(v:h_v(t)>0) h_v(t)>0.
```

In any `C`-valued cover with error below `gamma`, each active `v` has at
least one cutter positive at `t`.  Same-label orthogonality lets a label serve
at most one active `v`, so at least `m` labels are necessary.

If every `U_v` is connected but the ambient algebra `C` need not centralize
the ranges, colour the family `(U_v)` by the same subtree argument.  Choose
`g:[0,1]->[0,1]` with `g(0)=0` and `g(s)=1` for `s>=epsilon`, and give `v`
the single cutter `g(h_v)` in its graph colour.  This cutter commutes with
the range of `phi_v` because it is a function of its unit support.  The same
proof gives (T2)--(T3), recovering the earlier clause.

Finally, apply the component construction with half the target tolerance to
the outgoing maps of a nuclear approximation accurate to the other half.
Regroup the finite-dimensional summands by `k`.  The new outgoing map remains
contractive: its total unit support is bounded by the original one because
`sum_k c_(v,k)<=1` for every `v` and the hypothesis gives
`sum_v h_v<=1`.  With `m<=r+1`, this proves (T4).  In the
displayed interval example, colour the two components active over each of the
three disjoint bump supports with opposite labels; this gives two colours
although the unsplit graph is `K_3`.

**Trust boundary.**  Arbitrary component cutters require the common support
algebra to centralize the outgoing ranges.  Connected supports need no such
assumption because functional calculus of `h_v` supplies the cutter.  The
theorem does not claim that arbitrary essential extensions admit compact
R-tree geometry.
