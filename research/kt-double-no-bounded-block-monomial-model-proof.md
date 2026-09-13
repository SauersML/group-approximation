---
rg: 2
id: kt-double-no-bounded-block-monomial-model-proof
kind: route
title: A nonsofic group with trivial amenable radical has trivial soft kernel, so a bounded-block model would make it sofic
target: kt-double-admits-no-bounded-block-monomial-hs-model
requires:
  - block-monomial-hs-models-sofic-mod-amenable-soft-kernel
  - kt-pair-group-double-is-nonsofic
  - kt-q2-double-has-trivial-amenable-radical
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

Suppose `D` had a regular HS model `rho : D -> prod_omega U(k) wr S_n` with
`k` fixed.  Regularity makes `rho` injective.  By
`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`, the soft kernel `A`
of `rho` is an amenable normal subgroup of `D` and `D/A` is sofic.  By
`kt-q2-double-has-trivial-amenable-radical`, `A = 1`, so `D` is sofic.  That
contradicts `kt-pair-group-double-is-nonsofic` (Kun--Thom Theorem A, current
version, for the Theorem E pair with `q = 2`, `r, d >= 3`).  The finitary masa
form uses `diagonal-normalizer-rigidity` clause 1, as in the Leavitt case.
