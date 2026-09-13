---
rg: 2
id: number-field-linear-groups-act-properly-on-cat0-spaces
kind: claim
title: A finitely generated subgroup of GL_m over a number field acts properly on a proper CAT(0) space
distinct_from:
  every-braid-group-acts-properly-on-a-proper-cat0-space: that is the open non-cocompact reading of Problem 3.6 for braid groups; this is a general theorem about finitely generated groups linear over number fields, which would imply it for braid groups linear over a number field.
---

Let `F` be a number field and `G <= GL_m(F)` a finitely generated subgroup.
Then `G` acts properly by isometries (in the sense of Bridson–Haefliger) on a
proper, finite-dimensional, complete CAT(0) space. The space is a product of
Riemannian symmetric spaces `GL_m(R)/O(m)` and `GL_m(C)/U(m)` with
Euclidean Bruhat–Tits buildings of `GL_m` over finitely many `p`-adic
completions of `F`, each building taken with an extra factor `R`.

In particular, if some braid group `B_n` embeds in `GL_m(Z)`, or in `GL_m(F)`
for a number field `F`, then `B_n` acts properly on a proper CAT(0) space. So
Problem 3.2 connects to the non-cocompact reading of Problem 3.6 in both
directions:

- a yes for 3.2 gives `every-braid-group-acts-properly-on-a-proper-cat0-space`;
- a no for that claim gives a no for 3.2.

Linearity over a field of positive transcendence degree does not give this
conclusion, because the ring of entries is then not discrete in any finite
product of locally compact fields.

Proof: `number-field-linear-groups-act-properly-on-cat0-spaces-proof`.
