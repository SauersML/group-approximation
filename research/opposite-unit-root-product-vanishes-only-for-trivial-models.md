---
rg: 2
id: opposite-unit-root-product-vanishes-only-for-trivial-models
kind: claim
title: In characteristic two a homomorphism of EL_4 whose opposite unit root product n_JI(1) n_IJ(1) vanishes is trivial
distinct_from:
  el4-model-trivial-on-one-unit-root-element-is-trivial: that trivializes a model killing one root element; this trivializes a characteristic-two model in which one opposite product of unit root operators vanishes, by the braid relation, and uses that claim as its last step.
  index-three-corner-placement-holds-only-modulo-two-root-defects: that fixes the placement S(b) = n_31(b)n_13(1), T(a) = n_34(a)n_43(1) and isolates its deviation terms; this shows the placement's corner idempotent, the range idempotent of n_31(1)n_13(1), has positive rank in every nontrivial characteristic-two rank model.
  el3-unit-root-matrix-units-iff-two-root-identities: that forces the idempotents p_i = N_ij N_ji once the two-root identities hold; this shows the opposite products N_ji N_ij are nonzero in every nontrivial characteristic-two model, with no identity assumed.
artifacts:
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

**ESTABLISHED** (proof route `opposite-unit-root-product-triviality-proof`; artifact Section 5).
On paper, lane `w4-r4-corner`; verification requested from `w4-vf-gate`.

**Setting.**
- `R` and `M` are unital rings in which `2 = 0`.
- `sigma : EL_4(R) -> M^x` is a homomorphism, with `n_ij(r) = sigma(x_ij(r)) - 1`.

**Claim.** If `n_JI(1) n_IJ(1) = 0` for one pair `I != J`, then `sigma` is trivial.

**Consequences.**
- **Every opposite product is nonzero.** A nontrivial `sigma`, in particular one with nonzero
  two-root defect, has `n_JI(1) n_IJ(1) != 0` for every pair `I != J`.
- **Positivity for w4-r4-orth's placement.** When `M` is a rank ultraproduct over a field of
  characteristic two, every idempotent `e` with `e n_31(1) n_13(1) = n_31(1) n_13(1)` satisfies
  `rk(e) >= rk(n_31(1) n_13(1)) > 0`. So the corner idempotent of the placement in
  `index-three-corner-placement-holds-only-modulo-two-root-defects` is nonzero whenever `sigma` is
  nontrivial. For that placement check (iii) holds, and only the deviation terms stay open.
- **Scope.** Characteristic two only. In odd characteristic the braid relation involves `n_31(-1)`,
  which is not `n_31(1)`, and the argument below does not close.

## Attempts

Established, not open.
- **Braid step.** Expand the braid relation `x_13(1) x_31(1) x_13(1) = x_31(1) x_13(1) x_31(1)` in `M`,
  using `n_13(1)^2 = 0`. This gives `Y + XYX = X + YXY`, with `X = n_13(1)` and `Y = n_31(1)`.
- **Collapse.** If `YX = 0`, then `X = Y`.
- **Finish.** The Steinberg relation `[x_31(1), x_12(r)] = x_32(r)`, together with `x_13(1)`
  commuting with `x_12(r)`, kills `x_32(r)`. Normal closure then makes `sigma` trivial.
