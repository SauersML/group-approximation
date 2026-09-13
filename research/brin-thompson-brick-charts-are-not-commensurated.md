---
rg: 2
id: brin-thompson-brick-charts-are-not-commensurated
kind: claim
title: "For n >= 2 the standard brick charts are not commensurated by nV: breaks are codimension one"
invalidates: [brin-thompson-nv-a-t-menable-via-brick-charts]
---

Let `n >= 2`, and let `X_n` be the set of pairs `(U, φ)` with `U ⊆ C^n` clopen
and `φ: C^n → U` a homeomorphism in the Brin–Thompson groupoid, with `nV`
acting by postcomposition. Let `A_n ⊆ X_n` be the standard brick charts
`ι_B(u_1, ..., u_n) = (w_1 u_1, ..., w_n u_n)` for bricks
`B = [w_1] x ... x [w_n]`. Then some `g ∈ 2V <= nV` has `|g A_n \ A_n| = ∞`.
So the construction of `thompson-v-standard-cylinder-charts-are-commensurated`
does not extend to `nV`.

Sharper: if `g ∈ nV` is canonical on a brick partition whose `i`-th prefixes
have length `< W_i`, then every brick on which `g` is not canonical has some
prefix `w_i` of length `< W_i`. So the broken bricks lie in finitely many
codimension-one slabs of the product of trees. In general infinitely many
bricks of such a slab are broken.
