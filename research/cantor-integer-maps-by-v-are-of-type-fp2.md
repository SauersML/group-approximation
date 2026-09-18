---
rg: 2
id: cantor-integer-maps-by-v-are-of-type-fp2
kind: claim
title: "The group C(C,Z) ⋊ V is finitely presented, so the fixed-point test for FP_2 of the V-times-shift alternating group passes"
distinct_from:
  v-times-shift-fp2-forces-fp2-of-every-subshift-restriction: that proves FP_2 of A(G) would force FP_2 of C(C,Z) ⋊ V, and leaves open whether it holds; this proves it holds, so that necessary condition cannot kill the route.
  cantor-module-thompson-v-product-is-finitely-presented: that is the finite label group F_2, through centralisers of involutions in V (Martínez-Pérez–Matucci–Nucinkis); this is the infinite label group Z, where the centraliser theorem does not apply, through the one-point case of the abstract twisted Brin–Thompson finiteness theorems.
  labelled-thompson-groups-are-acyclic: that imports acyclicity of every labelled Thompson group V(G); this is a finiteness property of V(G), with no homology computed.
  cantor-integer-maps-by-v-have-haagerup-property: that asks for an analytic property of the same group; this is a finiteness property.
---

**ESTABLISHED** by `cantor-integer-maps-by-v-are-of-type-fp2-proof`
(2026-09-18, swarm-0917, not independently reviewed). The proof is short. No
novelty is claimed beyond reading the one-point case out of FFWZ Theorem 4.1(ii)
and Corollary 4.14.

## Statement

Let `C = {0,1}^N`. Thompson's `V` acts on `C` by prefix replacements, and on the
group `C(C, L)` of locally constant maps `C → L` (pointwise product) by
precomposition. Write `V(L) ≅ C(C, L) ⋊ V` for the labelled Thompson group.

1. If `L` is finitely presented, then `V(L)` is finitely presented. If `L` is of
   type FP_2, then `V(L)` is of type FP_2.
2. In particular, `C(C, Z) ⋊ V` is finitely presented, and hence of type FP_2.
3. Item 2 of `v-times-shift-fp2-forces-fp2-of-every-subshift-restriction` holds.
   That is the fixed-point restriction `C(C,Z) ⋊ V` of `A(G)`. So this necessary
   condition for `v-times-shift-alternating-group-is-of-type-fp2` cannot fail.

## Consequence for the route

`uncountably-many-simple-fp2-via-v-times-shift-restrictions` loses its cheapest
failure mode.
- The fixed point sees only the isotropy `Z` and none of the shift dynamics.
- So any obstruction to FP_2 of `A(G)` must come from the shift dynamics: from
  restrictions to infinite subshifts, or from `Σ` itself.
- The one known difficulty of that kind is the missing finite type system
  (`v-times-shift-groupoid-has-no-finite-similarity-types`), which rules out the
  standard Stein–Farley complex but proves nothing about FP_2.

## Not claimed

- **Periodic orbits of period `n ≥ 2`.** Nothing is claimed for restrictions
  there. The restricted groupoid should again be `G_V × Z` after cutting `C × Y`
  into `n` cylinders. It was not checked whether its full group is the image of
  `A(G)`.
- **Type `F_∞`.** No higher finiteness of `V(Z)` is claimed.
