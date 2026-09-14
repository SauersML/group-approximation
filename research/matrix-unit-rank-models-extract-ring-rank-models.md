---
rg: 2
id: matrix-unit-rank-models-extract-ring-rank-models
kind: claim
title: A matrix-unit rank model of EL_3 over a characteristic-p algebra extracts a rank model of the algebra, or is trivial
distinct_from:
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that concludes triviality for simple non-directly-finite rings in characteristic two; this extracts a unital ring homomorphism into a rank-ultraproduct corner for any coefficient algebra, so it applies under the no-rank-model hypothesis of the gate claim.
  matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial: that is the odd-characteristic triviality statement for simple non-directly-finite rings; this is the characteristic-free extraction step with no simplicity or finiteness hypothesis on the coefficients.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

Let `p` be a prime, `R` a unital algebra over a field of characteristic `p`, `M` a rank
ultraproduct over a field `k` of characteristic `p`, and `sigma : EL_3(R) -> M^x` a
homomorphism whose unit root elements act by matrix units
(`el3-unit-root-matrix-units-iff-two-root-identities`, condition 1).

1. If `p_1 != 0`, there is a unital ring homomorphism `C : R -> p_1 M p_1`, and `p_1 M p_1`,
   with rank renormalized by `rk(p_1)`, is a rank ultraproduct over `k`.
2. If `p_1 = 0`, `sigma` is trivial.

Proof: `research/artifacts/el3-two-root-identities-2026-09-12.md`, Section 2. It uses
Propositions 6 and 8 and the computation of Corollary 9 of
`research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`, none of which uses simplicity. Add
idempotent lifting in rank ultraproducts, and the normal closure of a unit root element in
`EL_3(R)`.
