---
rg: 2
id: finite-quotient-blindness
kind: claim
title: Finite quotients are blind to the compression
invalidates: [finite-quotient-models]
distinct_from:
  literal-mark-quotient-corona-blindness: This is the finite-quotient collapse of the compression data; that claim is its operator-norm corona counterpart, where the blindness is only tracial and is computed exactly.
---

`compressedImage_eq` (formalized). For any `φ` into a finite group, `φ(t)`
normalizes `φ(Γ)`; since `Γ` and the compressors generate, the image of `Γ`
is normal in every finite quotient. The compression data is quotiented away
before any finite-quotient construction starts. Specializes to
`⟨ā⟩ = ⟨ā²⟩` in every finite quotient of `BS(1,2)`. Manuscript:
`rem:finiteblind`.
