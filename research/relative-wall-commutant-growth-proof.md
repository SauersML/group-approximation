---
rg: 2
id: relative-wall-commutant-growth-proof
kind: route
title: Transport the wall by the compressor automorphism
target: relative-wall-commutant-growth
requires: []
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

`Ad pi(t)` carries `pi(Gamma)'` onto `pi(t Gamma t^(-1))'` by a two-line
computation, and one-sided compression gives the inclusion.  If the two
algebras agree, then for `v in N` the element `Ad pi(t)(v)` lies in `N` and
is fixed by `Ad pi(gamma)`, so `Ad pi(h)(v)=v` identically.  If they differ,
a unitary of `N_t` outside `N` fails to commute with some `pi(gamma)`, and
its `Ad pi(t)^(-1)`-preimage is a wall because the automorphism carries
`[v,pi(h)]` to `[w,pi(gamma)]`.  The involutive statement is the same
transport applied to a self-adjoint involution, using `t h t^(-1)=gamma`.
For the invariance form, no wall at any compressor gives
`Ad pi(s)(N)=N` for every `s in P_Gamma`; each such map then restricts to an
automorphism of `N`, so its inverse preserves `N` too, and the stabilizer of
`N` is a subgroup containing the generating set `P_Gamma`.  Complete argument
in the cited note, Lemma 1, Theorems 2 and 3, and Corollary 2a.
