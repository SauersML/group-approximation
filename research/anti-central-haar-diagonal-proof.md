---
rg: 2
id: anti-central-haar-diagonal-proof
kind: route
title: Halve every reflection by Thompson transitivity, then invert the sign-pattern Fourier transform
target: anti-central-rank-models-see-haar-measure-on-signed-diagonal
requires: [signed-thompson-algebra-is-odd-measure-crossed-product, odd-measure-space-has-no-honest-thompson-compression]
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

## Why sufficient

- **Half split.** For a proper nonempty clopen `C`, `σ(τ_(X∖C)) = −σ(τ_C)` because `σ(z) = −1`. Some Thompson
  element maps `C` onto `X∖C`, so the two eigen-idempotents of `σ(τ_C)` are conjugate and each has rank `1/2`.
- **Fourier inversion.** On a complete prefix code of size `n`, the Fourier coefficients of the joint rank law
  on sign patterns are `1` at the empty set, `−1` at the full set (all mass sits on odd patterns, since
  `τ_X = z`), and `0` elsewhere by the half split. Inverting gives `2^(1−n)` on every odd pattern.
- **Identification.** That is the normalized Haar measure on the atoms of `M_-` at that code, through the
  crossed-product identification. Ranks of orthogonal idempotents add, so the law agrees with `λ` on every
  clopen.

Details: artifact Section 4.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 54 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS. The assigned verifier remains `w3-vf-linear`.*
