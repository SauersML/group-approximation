---
rg: 2
id: stw82-tree-connected-supports-have-optimal-covers-proof
kind: route
title: Colour the subtree graph and cut above the vanishing spectral boundary
target: stw82-tree-connected-supports-have-optimal-covers
requires:
  - stw82-order-zero-direct-sum-support-criterion
---

Form the graph `G` on `V` by joining `v` and `w` when `U_v∩U_w` is
nonempty.  We first prove that `G` is `m`-colourable.

For every edge `vw`, choose a point `t_(v,w)∈U_v∩U_w`.  For each `v`,
let `K_v` be the convex hull in `T` of its finitely many incident chosen
points; for an isolated vertex choose any singleton in `U_v`.  Connected
subsets of a tree contain the unique arc between any two of their points,
so `K_v⊆U_v`.  The compact subtrees `(K_v)` have exactly the intersection
graph `G`: an edge supplies a shared chosen point, while a nonedge remains
disjoint because `K_v⊆U_v`.

Root `T` at a point `o`.  For each nonempty compact subtree `K_v`, let
`a_v` be its unique nearest point to `o`, and choose `v` for which
`d(o,a_v)` is maximal.  If `K_w` meets `K_v` at `z`, then `a_v` and `a_w`
both lie on the arc `[o,z]`.  Maximality places `a_w` no farther from `o`
than `a_v`, so

```text
a_v∈[a_w,z]⊆K_w.
```

Thus all neighbours of `v` contain `a_v` and form a clique.  Together
with `v` there are at most `m` of them, since every `K_w⊆U_w` containing
`a_v` contributes to (T1).  Remove `v` and repeat.  Reverse greedy
colouring uses at most `m` colours: when `v` is restored, its at most
`m-1` neighbours are pairwise adjacent and occupy distinct colours.
Let `k(v)` be the resulting colour.  Same-coloured cozero supports are
disjoint.

Fix `epsilon>0` and choose a continuous function `g:[0,1]→[0,1]` with

```text
g(0)=0,        g(t)=1 for t≥epsilon.
```

Set

```text
c_(v,k(v))=g(h_v),       c_(v,k)=0 for k!=k(v).
```

Functional calculus gives

```text
norm((1-g(h_v))h_v)≤epsilon,
```

proving (T2).  Every cutter is a function of `h_v`, which commutes with
the range of its order-zero map, so (T3) holds, including for square roots.
If `v!=w` have the same label, their cozero supports are disjoint; hence
`g(h_v)g(h_w)=0`, proving (T4).

Multiplication by `c_(v,k)` therefore gives a cpc order-zero map.  Its
difference from `phi_v` is a positive map whose norm is its value at the
unit, so (T2) gives the asserted approximation.  For fixed `k`, distinct
unit supports are orthogonal, and the direct-sum support criterion makes
their sum cpc order zero.

For optimality inside `C`, choose `t` at which (T1) is attained and put

```text
gamma=min_{v:h_v(t)>0} h_v(t)>0.
```

In any `C`-valued cover with error below `gamma`, every active `v` has
some label whose cutter is positive at `t`.  Same-label orthogonality lets
that label serve at most one active `v`, so at least `m` labels are needed.

Finally, apply the construction with half the target tolerance to the
outgoing maps of a nuclear approximation which is accurate to the other
half.  Regroup the finite-dimensional summands by `k(v)`.  The new outgoing
map is contractive because

```text
sum_v g(h_v)h_v ≤ sum_v h_v ≤1,
```

and it has `m≤r+1` order-zero colours.  This proves (T5).
