---
rg: 2
id: finite-quotient-blindness
kind: claim
title: Finite quotients are blind to the compression
invalidates: [finite-quotient-models]
distinct_from:
  literal-mark-quotient-corona-blindness: This is the finite-quotient collapse of the compression data; that claim is its operator-norm corona counterpart, where the blindness is only tracial and is computed exactly.
---

For any `φ` into a finite group, `φ(t)` normalizes `φ(Γ)`; since `Γ` and
the compressors generate, the image of `Γ` is normal in every finite
quotient.  *Formalization surface (corrected 2026-08-15):*
`GroupApproximation/Criterion/FiniteQuotientBlindness.lean` formalizes the
per-compressor statements (`compressedImage_le`, `compressedImage_eq`,
`compressorImage_normalizes`, `compressorImage_normalizes_inv`); the
generation-to-normality bridge (the normalizer is a subgroup containing a
generating set) is one line of group theory and is currently unformalized —
the earlier attribution of the full normality statement to
`compressedImage_eq` overstated the Lean surface. The compression data is quotiented away
before any finite-quotient construction starts. Specializes to
`⟨ā⟩ = ⟨ā²⟩` in every finite quotient of `BS(1,2)`. Manuscript:
`rem:finiteblind`.
