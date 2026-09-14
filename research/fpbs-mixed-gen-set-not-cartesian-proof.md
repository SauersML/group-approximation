---
rg: 2
id: fpbs-mixed-gen-set-not-cartesian-proof
kind: route
title: A generator moving both coordinates is an edge in neither factor
target: fpbs-mixed-gen-set-not-cartesian
requires: []
---

In a Cartesian product graph `X box Y` the vertex set is `V(X) x V(Y)` and every
edge changes exactly one coordinate: either an `X`-edge `(x,y)-(x',y)` or a
`Y`-edge `(x,y)-(x,y')`. In `Cay(H x K, S)` the edge from `g` to `g(h,k)` with
`h != 1` and `k != 1` changes both the `H`-coordinate (from the `H`-part of `g`
to `h` times it) and the `K`-coordinate simultaneously. Such an edge is neither
an `X`-edge nor a `Y`-edge of any Cartesian product whose factor moves are the
`H`- and `K`-translations, so `Cay(H x K, S)` is not that Cartesian product.
Hence any argument that decomposes percolation into a factor carrying the
nonamenability and a factor carrying the extra direction, and treats every edge
as belonging to one factor, has no verbatim analogue here.
