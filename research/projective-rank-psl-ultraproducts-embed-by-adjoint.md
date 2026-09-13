---
rg: 2
id: projective-rank-psl-ultraproducts-embed-by-adjoint
kind: claim
title: The adjoint representation embeds projective-rank ultraproducts of PSL_n(q) in rank ultraproducts of GL_(n^2)(q)
distinct_from:
  rank-modelled-simple-rings-give-linear-sofic-projective-el: that applies the same adjoint and commutant computation to elementary groups over rank-modelled simple rings; this states it for the groups PSL_n(q) with the projective rank length, as an embedding of metric ultraproducts.
  simple-group-support-and-semisimple-rank-models-collapse: that uses the adjoint to transfer collapse inequalities for tuples of one finitely presented group; this is a statement about ultraproducts, with no group presentation involved.
---

**ESTABLISHED (unreviewed)** by `projective-rank-psl-ultraproducts-embed-by-adjoint-proof`.

For `h in GL_n(F)` over a finite field, let `rho(h) = min_(lambda in F) rk(h - lambda)`. `l^pr(h) = rho(h)/n` is the
projective rank length on `PSL_n(q)` of Nikolov--Schneider--Thom (arXiv:1703.06092v2, p. 4). Let `Ad(h)` be
`X -> h X h^(-1)` on `M_n(F)`. Then:
1. `min(l^pr(h), 1/2) <= rk(Ad(h) - 1)/n^2 <= 2 l^pr(h)`.
2. For every sequence `(n_i, q_i)` and ultrafilter `U`, `Ad` induces an injective homomorphism
   `prod_U (PSL_(n_i)(q_i), l^pr) -> prod_U (GL_(n_i^2)(F_(q_i)), rk(. - 1)/n_i^2)`.
3. So a countable group that embeds in a projective-rank ultraproduct of groups `PSL_n(q)` is linear sofic over finite
   fields (definition on `simple-group-psl-width-is-finite-field-linear-soficity`).
