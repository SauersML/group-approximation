---
rg: 2
id: leavitt-el3-triviality-via-cohn-rank-inequality
kind: route
title: Small-defect Cohn data from a nonzero root defect, against the Cohn rank inequality, trivializes Leavitt EL_3 rank models
target: leavitt-el3-rank-models-over-finite-fields-are-trivial
requires:
  - two-root-defect-gives-small-defect-corner-cohn-family
  - corner-cohn-defects-bound-rank-in-rank-ultraproducts
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
  - leavitt-algebra-has-no-unital-rank-model
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

This route covers the instance `n = 2`, the same instance as
`leavitt-el3-triviality-via-rank-four-cuntz-family`. Let `K` be a finite field of characteristic
`p`, `R = L_K(1,2)`, and `sigma : EL_3(R) -> M^x` a homomorphism into a characteristic-`p` rank
ultraproduct.

1. **Both identities hold.** Suppose `N_12^2 != 0` or `N_23 N_12 != 0`.
   `two-root-defect-gives-small-defect-corner-cohn-family` then gives `x` with `rk(x) > 0`, elements
   `S_j in xM` and `T_i`, with total defect rank below `rk(x)`. This contradicts
   `corner-cohn-defects-bound-rank-in-rank-ultraproducts`. So `N_12^2 = 0` and `N_23 N_12 = 0`.
2. **Matrix units.** By `el3-unit-root-matrix-units-iff-two-root-identities`, the unit root
   elements act by matrix units.
3. **Triviality.** `matrix-unit-rank-models-extract-ring-rank-models` gives two cases:
   - a unital ring homomorphism `R -> p_1 M p_1` into a rank ultraproduct, which
     `leavitt-algebra-has-no-unital-rank-model` excludes for `K = F_2`;
   - or `sigma` is trivial.

So `sigma` is trivial.

**Scope of the last step.** `leavitt-algebra-has-no-unital-rank-model` is stated for `L_(F_2)(1,2)`.
Its proof (simplicity plus failure of direct finiteness, against a directly finite ultraproduct)
applies verbatim to `L_K(1,2)` for every field `K`. For `K != F_2` this route uses that verbatim
extension, as the rank-four route does.

**Difference from the rank-four route.** The step `R -> eMe` in the `D != 0` branch is replaced by
the rank inequality. That branch never uses completeness, idempotents, exact relations, or a corner
ultraproduct. It stays valid once the single open prerequisite
`two-root-defect-gives-small-defect-corner-cohn-family` is established; the other four requirements
are established.
