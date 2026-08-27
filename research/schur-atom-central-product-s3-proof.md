---
rg: 2
id: schur-atom-central-product-s3-proof
kind: route
title: Identify the relative commutator with the S3 jump sign and use its balanced endpoint half
target: schur-atom-central-product-has-s3-endpoint-split
requires:
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - relative-pauli-child-split-gives-one-exit-copy
  - six-generator-one-jump-router-has-s3-radical-atlas
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - finite-group-shared-overlap-polar-alignment
---

The corrected pair satisfies `[P_a,Q_a]=K=-1` on `p_aQ`.  Since the two
central-product factors commute, `p_aQ` reduces the S3 packet.  In the marked
`K=-1` S3 sector, a packet word `c` satisfies `[b,c]=J=-1`; conjugation by
`c` exchanges the two `b` spectral halves while preserving `p_aQF`.  This
proves `(SCP2)`.

On `K=+1`, the endpoint word `b` is radical and its two characters are the
two allowed affine atoms.  On `K=-1`, its two spectral halves are the active
and exit atoms.  `s3-active-complement-is-three-equal-scale-affine-atoms`
shows that all four have the same four-dimensional spin scale.  Combining
this with the Schur relative-pair restriction identity `(PCS4)` proves
`(SCP3)` and shows that the exit costs at most one source copy.

A central product over an embedded central subgroup injects both factors.
Given a marked Schur representation, decompose over the finite `<J,K>`
characters, amplify each summand countably, and tensor it with the matching
S3 representation.  This extends the original action and proves exact marked
completeness.  For approximate matrices, fixed-finite-group exactification
and shared-center polar alignment change every degree-bounded endpoint
projection by `O(sqrt(E))`; trace and transport estimates follow by product
telescoping.

