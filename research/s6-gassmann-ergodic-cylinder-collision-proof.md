---
rg: 2
id: s6-gassmann-ergodic-cylinder-collision-proof
kind: route
title: Compare the four-support and perfect-matching Klein subgroups of S6
target: ergodic-irs-character-forgets-joint-cylinders
requires: []
---

Both groups in `(EGC3)` have order four and their three nonidentity elements
all have cycle type `2^2`. Therefore they meet every conjugacy class of
`S_6` in the same number of elements: one in the identity class, three in
the double-transposition class, and zero in every other class.

For a finite group `G`, a subgroup `H`, and the uniform IRS `theta_H` on the
conjugates of `H`, double counting gives

```text
theta_H({K:g in K})=|g^G intersect H|/|g^G|.           (EGP1)
```

Hence the equal conjugacy-class intersections of `H_1,H_2` prove `(EGC1)`.
Concretely, every double transposition has membership probability
`3/45=1/15` and every other nonidentity element has probability zero.

The conjugates of `H_1` are indexed by four-element supports, so there are
`binom(6,4)=15` of them. The conjugates of `H_2` are indexed by perfect
matchings of six points, also a set of size `15`. Put

```text
a=(12)(34),   b=(13)(24).                              (EGP2)
```

The elements `a,b` generate `H_1`, so exactly one conjugate of `H_1`
contains both. This gives probability `1/15`. A perfect-matching Klein group
has as its nonidentity elements the three pairwise products of the matching
edges. No such group can contain both `a` and `b`: the first would force
matching edges `12,34,56`, while the second would force incompatible edges
`13,24`. Thus the `H_2` probability is zero, proving `(EGC2)`.

Finally, uniform measure on a finite conjugacy orbit is ergodic. Equivalently,
`theta_i` is the stabilizer distribution of the transitive action of `S_6`
on `S_6/H_i`. This proves the claimed ergodic collision.
