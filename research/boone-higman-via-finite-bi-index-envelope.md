---
rg: 2
id: boone-higman-via-finite-bi-index-envelope
kind: route
title: Give the simple core finite bi-index and take the twisted Brin-Thompson group of the coset action
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, chatterji-kassabov-normal-generator-embedding, simple-core-bi-index-counts-coset-action-pair-orbits, ck-envelope-simple-core-has-finite-bi-index, twisted-brin-thompson-finite-presentation-criterion]
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `G` be finitely generated with solvable word problem.  Build
`G <= S <= Gamma` as in `boone-higman-via-ck-maximal-kernel`, using
`boone-higman-thompson-simple-envelope` and
`chatterji-kassabov-normal-generator-embedding`, but arranged by
`ck-envelope-simple-core-has-finite-bi-index` so that
`|S \ Gamma / S| < infinity`.

If `S = Gamma` then `Gamma` is already a finitely presented simple group
containing `G` and we are done.  Otherwise consider `Gamma` acting on
`Gamma/S`.  By `simple-core-bi-index-counts-coset-action-pair-orbits` the
action is faithful, its point stabilizer is `S`, and its orbits on ordered
pairs are the double cosets, hence finitely many.  `Gamma` is finitely
presented and `S` is finitely generated.

By `twisted-brin-thompson-finite-presentation-criterion` the twisted
Brin--Thompson group `SV_Gamma` is finitely presented, and faithfulness makes
it simple.  It contains `Gamma`, hence `S`, hence `G`.

## Why every prerequisite is genuinely used

The two envelope theorems supply the group `Gamma` and the simple core inside
it.  The bi-index claim is the only open input and supplies the pair-orbit
finiteness.  The coset-action claim supplies faithfulness — which is not
automatic and is the one place the near-solution is consumed, because without
it the action could have a large kernel and the twisted Brin--Thompson group
would be relatively simple rather than simple.  The imported criterion
supplies the conclusion.

## How this differs from the first route, and why both are kept

`boone-higman-via-ck-maximal-kernel` needs a compactness property of the
normal lattice.  This route needs a finiteness property of a double coset
space.  Neither is known and neither implies the other by any argument found
in the audit, so they are independent attacks on the same target rather than
variants of one.

The honest comparison: the first route's open claim is about an object with
no handles (an arbitrary maximal normal subgroup, produced by Zorn), while
this route's is about an object one can in principle compute with (double
cosets of a matrix group over the explicit finitely presented ring `U` of
`universal-sandwich-ring-is-finitely-presented-and-injective`).  Against
that, the first route needs its finiteness only for *one* maximal subgroup
while this one needs a global bound, and the known construction offers no
reason to expect it.
