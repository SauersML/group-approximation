---
rg: 2
id: brin-thompson-nv-stein-farley-complex-is-not-cat0-proof
kind: route
title: "Three vertices of the nV expansion complex have no median"
target: brin-thompson-nv-stein-farley-complex-is-not-cat0
requires: []
---

Work with the first two coordinates `x, y`; other coordinates are carried along
unsplit. Every edge changes the number of pieces by exactly one, so
`d(v, w) >= |#v - #w|`.

Vertices:

- `v_0`: the one-piece partition `{C^n}` with the identity chart;
- `v_x`: `{[0] x C, [1] x C}`, the split of `v_0` along `x`;
- `v_y`: `{C x [0], C x [1]}`, the split along `y`;
- `q`: the four quadrants `[a] x [b]` with canonical charts.

Splitting `v_x` along `y` in both halves gives `q`, and so does splitting `v_y`
along `x` in both halves. The results agree as vertices: the same four pieces
with the same canonical charts, up to permutation.

Distances:

- `d(v_0, v_x) = d(v_0, v_y) = 1`;
- `d(v_x, q) = d(v_y, q) = 2`, realized by one square, with lower bound
  `4 - 2`;
- `d(v_0, q) = 3`;
- `d(v_x, v_y) = 2`: they have the same piece count, so they are not adjacent,
  and `v_0` is a common neighbour.

A median `m` of `v_x, v_y, q` must satisfy
`d(v_x,m)+d(m,v_y) = 2`, `d(v_x,m)+d(m,q) = 2`, `d(v_y,m)+d(m,q) = 2`.
Adding gives `d(v_x,m)+d(v_y,m)+d(q,m) = 3`, so `m` lies on a geodesic from
`v_x` to `v_y`.

Common neighbours of `v_x` and `v_y` have 1 or 3 pieces. A 3-piece neighbour of
`v_x` contains the piece `[0] x C` or `[1] x C`; one of `v_y` contains
`C x [0]` or `C x [1]`. No partition contains both. So `v_0` is the only common
neighbour, and the geodesic vertices are `v_x, v_0, v_y`.

- `m = v_0` gives `d(v_x,m)+d(m,q) = 1+3 = 4`.
- `m = v_x` gives `d(v_y,m)+d(m,q) = 2+2 = 4`.
- `m = v_y` is symmetric.

No median exists.
