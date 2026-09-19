---
rg: 2
id: giol-kerr-flat-name-local-colourings-give-uniform-gamma
kind: route
title: Flat name-local return-tower colourings give Giol-Kerr uniform Gamma
target: giol-kerr-crossed-products-have-uniform-gamma
requires:
  - giol-kerr-return-towers-admit-flat-name-local-colourings
---

Fix `n>=2`. Apply the required finite-stage statement to an increasing
dense sequence of self-adjoint finite subsets of `C(X)` and tolerances
tending to zero. The assembled contractions define projections
`p_1,...,p_n` in the uniform tracial ultrapower. The partition clauses
give pairwise orthogonality and `sum_r p_r=1`; name-locality gives
commutation with `C(X)`; and the seam estimate gives commutation with the
implementing unitary. Hence `p_r` lies in `A^omega intersect A'`.

Flat diagonal gives, for every invariant measure `mu`, every `f in C(X)`,
and every `r`,

`tau_mu(f p_r)=tau_mu(f)/n`.

This diagonal identity already forces the full uniform-Gamma identity.
Indeed, take any generalized limit trace `tau=lim_omega tau_(mu_m)` and
put

`phi_r(a)=lim_omega tau_(mu_m)(a q_(m,r))`.

Centrality makes `phi_r` a positive tracial functional, and flatness says
`phi_r|_(C(X))=(tau|_(C(X)))/n`. For a free action of `Z`, every trace
on `C(X) rtimes_h Z` is uniquely determined by its restriction to
`C(X)`: traciality and topological freeness kill every coefficient
`f u^k`, `k!=0`. Therefore `phi_r=tau/n` on all of `A`. This holds for
every generalized limit trace, so the `p_r` witness uniform property Gamma.

The route is direct. It does not use the open Giol--Kerr/Villadsen
tracial-completion identification, and it does not try to promote the false
Cartan-relative Gamma statement.
