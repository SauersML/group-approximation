---
rg: 2
id: brin-thompson-nv-embeds-in-mv-proof
kind: route
title: "Products of canonical brick maps with the identity are canonical brick maps"
target: brin-thompson-nv-embeds-in-mv
requires: []
---

Let `g ∈ nV` be canonical on the brick partition `B_1, ..., B_k` of `C^n`. Then
`G = g x id_{C^{m-n}}` is canonical on the partition `B_i x C^{m-n}` of `C^m`:
on each piece it is the product of `g`'s prefix replacements with the empty
prefix replacement in the remaining `m - n` coordinates. It maps these pieces
onto the bricks `g(B_i) x C^{m-n}`, which partition `C^m`. So `G ∈ mV`.
`(g h) x id = (g x id)(h x id)` and `g x id = id` only for `g = id`, so the map
is an injective homomorphism.
