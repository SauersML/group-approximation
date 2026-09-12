---
rg: 2
id: anti-central-rank-models-see-haar-measure-on-signed-diagonal
kind: claim
title: An anti-central characteristic-three rank model of the ternary Leavitt unit group restricts to Haar measure on the signed diagonal
distinct_from:
  odd-measure-space-has-no-honest-thompson-compression: that shows the Haar measure on the odd-measure space is Thompson-invariant and forbids honest compressions inside the crossed product; this shows every anti-central rank model restricts to that Haar measure on the diagonal, so the law is forced rather than chosen.
  anti-central-rank-models-kill-ternary-corner-witnesses: that extracts the single state value 1/2 on the swap idempotent from the dihedral halving; this computes the whole rank law of the model on the commutative algebra of reflections.
artifacts:
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 4). `gk-vf-linear` independently re-derived it, PASS
with no corrections (Section 54 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`).
Verification by `w3-vf-linear` is also requested. Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = −1`, and let `H = E ⋊ V` be the signed Thompson
group of `signed-thompson-algebra-is-odd-measure-crossed-product`, with
`F_3[H] eps_- ≅ C(M_-, F_3) ⋊ V`.

Let `Γ <= G` contain `H`, and let `σ : Γ -> M^x` be a homomorphism into the units of a rank ultraproduct over
fields of characteristic three, with `σ(z) = −1`. Then for every clopen `U` of `M_-`, the image of the
indicator `1_U` has rank `λ(U)`, the normalized Haar measure. In particular:
- **Reflections.** For every proper nonempty clopen `C`, both eigen-idempotents of the involution `σ(τ_C)`
  have rank `1/2`.
- **Prefix codes.** For a complete prefix code of size `n`, the joint eigen-idempotents of the reflections
  of its leaves have rank `2^(1−n)` on sign patterns with an odd number of minus signs, and `0` on the
  others.

Consequences:
- By `ternary-leavitt-rank-models-move-z-iff-nontrivial`, every nontrivial characteristic-three rank model of
  `G` yields such a model. So a positive answer to
  `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model` must carry this law.
- It recovers the corner exclusion of `anti-central-rank-models-kill-ternary-corner-witnesses` on subgroups
  containing `H`: the cylinder idempotent `q_0` has rank `1/2 < 1`.

Proof: route `anti-central-haar-diagonal-proof`.
