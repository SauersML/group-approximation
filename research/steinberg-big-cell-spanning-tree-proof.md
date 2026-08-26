---
rg: 2
id: steinberg-big-cell-spanning-tree-proof
kind: route
title: Complement the opposite big cell by an explicit projective-plane spanning tree
target: steinberg-cycles-have-big-cell-chord-coordinates
requires:
  - steinberg-fox-kernel-is-flag-incidence
---

Write

```text
N=p^2+p+1                                                   (SBP1)
```

for the common number of points and planes in `F_p^3`.  There are `p+1`
points on every plane and `p+1` planes through every point.

Let `T_1` be the flags whose point lies in `H_0`, and `T_2` the flags whose
plane contains `z`.  Then

```text
|T_1|=|T_2|=(p+1)^2.                                      (SBP2)
```

In their intersection, the point can be `z`, giving `p+1` flags, or one of
the other `p` points of `H_0`, in which case the only plane containing it and
`z` is `H_0`.  Therefore

```text
|T_1 intersect T_2|=2p+1,
|T|=2(p+1)^2-(2p+1)=2N-1.                                (SBP3)
```

The subgraph `T` contains every vertex.  A point outside `H_0` is joined to
the plane it spans with `z`, while a plane not containing `z` is joined to a
point in its nonzero intersection with `H_0`.  The two families meet along
the flags counted above, and within them the point `z` and plane `H_0`
connect all such choices.  Hence `T` is connected.  It has `2N` vertices and
`2N-1` edges, so it is a tree.

A flag lies outside `T` precisely when its point has nonzero first
coordinate and its plane covector has nonzero third coordinate.  Normalize
both coordinates.  Writing the point as `[1:a:b]` and the covector as
`[d:-c:1]`, incidence forces `d=ac-b`.  This proves the unique parametrization
`(SBC2)` and shows that there are `p^3` chords.

For any oriented graph with a fixed spanning tree, restriction from the
cycle space to the coefficients of the complementary chords is an
isomorphism.  Indeed, after chord coefficients are fixed, the zero-boundary
equations on the tree have a unique solution: delete a tree edge and sum the
prescribed chord boundary demands over one of the resulting components.
This gives its coefficient with the sign dictated by the edge orientation.
The cut formula uses only `0,+1,-1`, proving `(SBC3)` over every coefficient
field and defining `E_p`.

More explicitly, orient every tree edge from its point endpoint `P` to its
plane endpoint `H`.  Let `d=partial(c_f)` be the boundary demand of the chord
chain, and let `K_H(e)` be the component containing `H` after deleting
`e=(P,H)`.  Then

```text
(E_pf)(e)=-sum_(v in K_H(e)) d(v).                     (SBP4)
```

The branches in `(SBP4)` are completely elementary.  Points outside `H_0`
are leaves attached to `span(P,z)`; planes not containing `z` are leaves
attached to `H intersect H_0`.  After removing those leaves, `H_0` is joined
to every point of `H_0`, and `z` is joined to every plane containing `z`.
Thus a noncentral cut contains one such leaf, or one center arm together
with its leaves; the central cut is the `H_0` half of this double star.  This
is the promised explicit boundary rule for every zero denominator in
`(SCA2)`.

For a chain `F=E_p f` and a chord `C`, the coefficient of `gF` at `C` is the
coefficient of `F` at `g^(-1)C`.  If the latter is a chord this is one entry
of `f`; if it is in `T` it is the cut formula just proved.  This establishes
`(SBC4)`.  Conjugating the expansions `(SFI2)` by `R_p,E_p` gives `(SBC5)`.
