---
rg: 2
id: parity-carrier-density-is-already-terminal
kind: route
title: Stop after placing positive old-commutant density in the canonical marked corner
target: schur-amplified-parity-compressor-hs-return
requires:
  - toeplitz-parity-compressor-candidate
  - parity-compressor-old-commutant-has-positive-density
  - canonical-marked-corner-kazhdan-density-vanishes
---

Apply the coefficient-covariant extension promised by
`parity-compressor-old-commutant-has-positive-density` to canonical
microstates of its group.  The central sign has canonical negative mass
`1/2`, so its forbidden carrier mass `q` is bounded below.  Formula `(PCD1)`
then supplies, as the relator defect tends to zero, an old
`Lambda`-low-commutator subspace of adjoint density bounded below by a fixed
positive constant.

This contradicts `(CMK1)` directly.  The exact marked model and the
injectivity requirement remain those of the packet extension in the target
claim.  The parity-twist copy and the relative commutant-growth estimate are
not used in the normalized-HS soundness step.
