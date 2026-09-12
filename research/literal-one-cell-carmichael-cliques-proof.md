---
rg: 2
id: literal-one-cell-carmichael-cliques-proof
kind: route
title: Bound the clique by the axes of conjugates of a primitive generator
target: literal-one-cell-carmichael-cliques-are-uniformly-finite
requires: []
---

Use the Cayley tree `T` of `F` in the basis `X`.  A conjugate of the primitive
generator `b` is a translation of length one on an oriented translate of the
`b`-axis.  Distinct conjugates have distinct oriented axes; the unoriented
axes are distinct cosets of `<b>` and are disjoint.

For two length-one translations `u,v` with distinct axes, simultaneously
conjugate so that `u=b` and write `v=g^(-1)b g`.  Choose a shortest
representative `g_0` of the double coset `<b>g<b>`.  Its length is the bridge
distance between the two axes.  The remaining right `<b>` power merely slides
the second bridge endpoint along the first axis and disappears after cyclic
reduction.  Since the first and last letters of `g_0` are not `b^(+-1)`, the
word

```text
b g_0^(-1) b g_0
```

is cyclically reduced.  Hence

```text
cyc_len(uv)=2+2|g_0|.                                   (LOC2)
```

Also `b` is not conjugate to `b^(-1)` in `F`, so `uv` is nontrivial, and
unique roots in a free group give

```text
cyc_len((uv)^2)=2 cyc_len(uv).                            (LOC3)
```

Thus `(LOC1)` bounds the distance between every pair of axes by a constant
`R=R(L)`.

For each axis `A` take its closed `R`-neighborhood in `T`.  These are convex
subtrees, and the distance bound makes them pairwise intersect.  Convex
subtrees of a tree have the finite Helly property, so all these neighborhoods
contain one common vertex `z`.  Hence every axis meets the finite ball
`B_T(z,R)`.  Every vertex of the Cayley tree lies on a unique translate of
the `b`-axis, and each such axis has only two orientations.  The number of
oriented `b`-axes meeting this ball is therefore at most `2|B_T(z,R)|`, a
constant `K(F,L)` independent of `S`.  This proves the first statement.

If every `(u_i u_j)^2` is a conjugate of a word in a fixed finite list `Q`,
then `(LOC1)` holds with

```text
L=max_(q in Q) cyc_len(q).
```

The uniform clique bound therefore rules out arbitrarily large literal
one-cell Carmichael families.
