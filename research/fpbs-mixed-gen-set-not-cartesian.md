---
rg: 2
id: fpbs-mixed-gen-set-not-cartesian
kind: claim
title: A mixed generating set of a direct product is not a Cartesian product graph
invalidates:
  - fpbs-dead-product-peres-all-gens
---

**ESTABLISHED.** Let `G = H x K` and let `S` be a finite symmetric generating
set of `G` that contains an element `(h,k)` with `h != 1` and `k != 1`. Then
`Cay(G,S)` is not isomorphic, as a graph, to any Cartesian product
`X box Y` in which the two factor edge-directions are the `H`- and `K`-moves.
Equivalently, `Cay(G,S)` carries an edge that projects nontrivially to both
factors and so belongs to no single factor.

Consequently the mechanisms that prove `p_c < p_u` for the product generating
set -- Grimmett--Newman for `T_k x Z^d`, the nonunimodular route
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`, and Peres's uniqueness-
threshold argument for `X x Y` -- do not apply verbatim to `Cay(G,S)`, because
each uses that every edge is a move in exactly one factor. This is precisely why
the every-generating-set statement `fpbs-product-every-generating-set` is not a
corollary of the product-generating-set results, and it kills the naive route
`fpbs-dead-product-peres-all-gens`.

The obstruction is not a claim that `p_c < p_u` fails for mixed generating sets;
it is only that the Cartesian-product proof structure is unavailable and a
generating-set-transfer argument is required instead.

DERIVATION
fpbs-mixed-gen-set-not-cartesian-proof
