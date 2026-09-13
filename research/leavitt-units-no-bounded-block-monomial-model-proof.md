---
rg: 2
id: leavitt-units-no-bounded-block-monomial-model-proof
kind: route
title: Push a block-monomial model through its permutation part, then read the soft kernel of a simple nonsofic group
target: leavitt-units-admit-no-bounded-block-monomial-hs-model
requires:
  - block-monomial-hs-models-sofic-mod-amenable-soft-kernel
  - leavitt-unit-group-has-only-trivial-sofic-morphisms
  - openai-leavitt-unit-nonsofic
  - binary-leavitt-elementary-group-is-simple
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

(1) By the Hamming comparison in
`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`, the permutation
parts of `rho` form a homomorphism `R^x -> prod_omega (S_n, d_H)`, a universal
sofic group.  It is trivial by `leavitt-unit-group-has-only-trivial-sofic-morphisms`.
So the soft kernel is all of `R^x`, and by the exact identity
`||(u; sigma) - (u; id)||_2^2 = 2 d_H(sigma, id)` each `rho(g)` is represented by
its block-diagonal part.

(2) Let `H >= E ≅ EL_9(R)` and suppose `H` has a regular `U(k) wr S_n` model
with `k` fixed.  Restricting it to `E` keeps it regular and block-monomial.
`E` is simple (`binary-leavitt-elementary-group-is-simple`, `9 >= 3`) and
nonsofic.  Indeed `openai-leavitt-unit-nonsofic` produces the nonsofic group
`G = EL_D(R) ≅ EL_9(R)`, and the sofic-morphism node records
`EL_n(R) ≅ R^x` for `n >= 3`.  A nonsofic group is not amenable, so the
amenable radical of the simple group `E` is trivial.  The corollary of the
soft-kernel theorem then makes `E` sofic, a contradiction.  For `k = 1` the
finitary masa form follows from `diagonal-normalizer-rigidity` clause 1, which
moves microstates with small `def_D` to monomials at cost `3 sqrt(def_D)`.

In the ultraproduct form (2) already follows from (1): a regular model with
`A = R^x` would make `R^x` amenable.  Route (2) through `EL_9(R)` covers every
overgroup at once.
