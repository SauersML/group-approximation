---
rg: 2
id: hyperlinear-fp-simple-via-amenable-orbit-full-group
kind: route
title: A finitely presented simple group realized in an amenable orbit full group is sofic, hence hyperlinear
target: hyperlinear-fp-infinite-simple-group
requires:
  - fp-simple-group-in-amenable-orbit-full-group
  - amenable-orbit-full-group-subgroups-are-sofic
  - sofic-implies-hyperlinear
---

Let `S`, `Lambda ~ (X, mu)` and `rho` be as in
`fp-simple-group-in-amenable-orbit-full-group`.

1. **Faithful modulo null sets.** `K = {g : rho(g) = id almost everywhere}` is a
   normal subgroup of `S`. Some element acts nontrivially on a set of positive
   measure, so `K != S`, and simplicity gives `K = 1`. Hence
   `mu(Fix rho(g)) < 1` for every `g != 1`.
2. **Sofic.** `amenable-orbit-full-group-subgroups-are-sofic` applies to `rho`.
3. **Hyperlinear.** `sofic-implies-hyperlinear`.

So `S` is a finitely presented infinite simple sofic group, which meets the root
with the preferred strengthening "sofic". Torsion-freeness is not supplied.

The route is independent of `hyperlinear-fp-simple-via-amenable-example`: it
consumes no amenability of `S`.
