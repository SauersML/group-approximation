---
rg: 2
id: ternary-rank-model-root-element-torus-normal-form
kind: claim
title: In characteristic three a root element of a rank model is a torus-weight flip minus its square
distinct_from:
  el3-unit-root-matrix-units-iff-two-root-identities: that characterizes matrix-unit models by two identities over any rings; this gives the characteristic-three torus normal form of every rank model and reduces the first identity to the vanishing of the square of the weight-flipping part.
artifacts:
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 5). `gk-vf-linear` independently re-derived it, PASS
with no corrections (Section 54 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`).
Verification by `w3-vf-linear` is also requested. Let `R = L_(F_3)(1,2)` and `G = R^x = GL_3(R) = EL_3(R)`, identified through the prefix code
`(0, 10, 11)`, so that `x_12(1) = 1 + S[0]T[10]`. The constant sign matrices form
`T_3 = <τ_0, τ_10, τ_11>`, with `τ_0 τ_10 τ_11 = z = −1`.

Let `σ` be any homomorphism from `G` into the units of a characteristic-three rank ultraproduct. Let `P_ε`,
`ε` in `{±}^3`, be the joint eigen-idempotents of `σ(T_3)`, `N = σ(x_12(1)) − 1`, and `A` the part of `N`
mapping each `P_ε` to `P_(ε')`, where `ε'` flips the first two signs. Then:
- `N = A − A^2`, `A^3 = 0`, and `A^2` preserves every weight space;
- `N^2 = A^2`, so the identity `N_12^2 = 0` holds exactly when `N` has no weight-preserving component;
- if `σ(z) = −1`, the only weight spaces are `(−,+,+)`, `(+,−,+)`, `(+,+,−)` and `(−,−,−)`, each of rank
  `1/4` (`anti-central-rank-models-see-haar-measure-on-signed-diagonal`), and `A` exchanges the first two
  and the last two.

The proof uses only the three reflections and `x_12(1)^3 = 1`. Projective content of level groups violates
`A^2 = 0` while meeting the Haar law, so finite level groups cannot force the identity.

Proof: route `ternary-root-element-torus-normal-form-proof`.
