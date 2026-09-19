---
rg: 2
id: affine-s3-active-idempotent-toeplitz-envelope-proof
kind: route
title: Centralize the active orbit and use it as the one-sided Toeplitz cokernel
target: affine-s3-active-idempotent-toeplitz-envelope
requires:
  - affine-s3-endpoint-permutes-active-atoms
  - schur-idempotent-is-an-injective-toeplitz-defect
  - schur-toeplitz-envelope-has-proper-self-embedding
  - schur-toeplitz-root-mark-is-fd-invisible
---

The active sum is fixed by the affine `S_3` and already commutes with `D`, so
it is central in `k[C_aff]`.  Clifford theory for the transitive orbit gives
stabilizer `C_2`; inducing its two one-dimensional representations gives the
two degree-three blocks in `(ATE2)`.  The forbidden atom and the unmarked
sector show that the active central idempotent is proper.

The proofs of `schur-idempotent-is-an-injective-toeplitz-defect` and
`schur-toeplitz-envelope-has-proper-self-embedding` use only that the chosen
idempotent is nonzero, proper, central, and killed by an augmentation.  Those
hypotheses hold for `A`, because it lies in the `J=-1` sector whereas the
trivial character has `J=+1`.  They therefore apply verbatim to `(ATE3)` and
`(ATE4)`.

Finally, the finite-dimensional root-kernel proof of
`schur-toeplitz-root-mark-is-fd-invisible` also uses only the characteristic-
`p` Steinberg relations and the fact that directly finite coefficient
quotients kill the designated defect.  It applies with `P_f` replaced by
`A`, proving every clause of `(ATE5)`.
