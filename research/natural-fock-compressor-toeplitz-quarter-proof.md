---
rg: 2
id: natural-fock-compressor-toeplitz-quarter-proof
kind: route
title: Functoriality of the exterior algebra and the contraction formula for transvections give a defect of rank one quarter
target: natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter
requires:
  - natural-compressor-extension-fails-at-toeplitz-commutator
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/fock-local-rank-models-2026-09-12.md
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

Section 3 of the Fock artifact, Proposition 3.1.

1. **Functoriality.** `Λ` is a group homomorphism `GL(W) -> GL(Λ(W))`, so it carries the Proposition 7
   identity `Z^^(−1)[X^, Y^] = u_13(N−1, N−1)` to the Fock space.
2. **Contraction.** For `u = 1 + v ⊗ φ` with `φ(v) = 0`, expanding `∧(w_i + φ(w_i)v)` kills every term with
   two factors `v`. So `Λ(u) − 1 = v ∧ i_φ`.
3. **Counting.** In a basis `v, e_2, e_3, ...` with `φ(e_2) = 1` and `φ(e_{>=3}) = 0`, the image is spanned by
   `v ∧ ω'` with `ω' ⊆ {e_3, ...}`. That is `2^(n−2)` monomials, a quarter of `Λ`, and a quarter of each
   parity.

*Verification by `w3-vf-linear` (2026-09-12), Section 28.3 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Λ(1+v⊗φ) − 1 = v∧i_φ, which sends e_2∧ω' to e_1∧ω' for ω' ⊆ {3..n}: rank 2^(n−2) = dim/4, degree-preserving, with 2^(n−3) monomials on each parity.*
