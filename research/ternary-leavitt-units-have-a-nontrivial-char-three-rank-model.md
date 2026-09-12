---
rg: 2
id: ternary-leavitt-units-have-a-nontrivial-char-three-rank-model
kind: claim
title: The ternary Leavitt unit group has a nontrivial rank model in characteristic three
refuted_by:
  - ternary-anti-invariant-swap-corner-is-full
  - leavitt-el3-rank-models-over-finite-fields-are-trivial
distinct_from:
  projective-ternary-group-is-f3-linear-sofic: that is F_3-linear soficity of the scalar quotient, which needs separating approximations and implies this; this asks only for one nontrivial homomorphism into a characteristic-three rank ultraproduct, from the unit group or equivalently from the quotient.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the characteristic-two gate for the binary unit group, where there are no scalars to move; this is the characteristic-three gate, where the central involution adds structure.
artifacts:
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

**OPEN.** `G = L_(F_3)(1,2)^x` has a nontrivial homomorphism into the units of a rank ultraproduct of
matrix algebras over fields of characteristic three.

By `ternary-leavitt-rank-models-move-z-iff-nontrivial`, this is the same as a model moving `z = −1`, an
injective model, an anti-central model, or a nontrivial model of `PG = G/{±1}`.

**Payoffs.**
- **Yes** refutes `ternary-anti-invariant-swap-corner-is-full` (artifact Corollary 3.1).
- **No** means every characteristic-three rank model of `G` and of `PG` is trivial, so neither is
  `F_3`-linear sofic. It is the characteristic-three instance of
  `leavitt-el3-rank-models-over-finite-fields-are-trivial`, since `G = GL_3(R) = EL_3(R)`.

## Attempts

- **Moving `z` is not an extra condition** (w3-gate-char3). Artifact Section 2: nontrivial models become
  injective and z-moving along the corner embedding, and anti-central models square to models of `PG`.
- **Corner locality** holds in characteristic three (artifact Remark 3.4). A proof of "no" may work on any
  corner copy, but its extraction step needs both `N_12^2 = 0` and `N_23 N_12 = 0`.
