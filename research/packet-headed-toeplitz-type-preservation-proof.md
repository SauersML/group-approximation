---
rg: 2
id: packet-headed-toeplitz-type-preservation-proof
kind: route
title: Compress and decompress each forbidden coefficient by y to the n and x to the n
target: packet-headed-toeplitz-shift-is-schur-type-preserving
requires:
  - schur-toeplitz-envelope-has-proper-self-embedding
  - schur-toeplitz-head-is-matrix-amplified-forbidden-algebra
---

The forbidden coefficient ideal lies in the kernel of the augmentation, so
the head correction in `sigma` vanishes on it. Iteration gives `(PTS2)`.
Because `y^nx^n=1`, decompression recovers `a`; compression after
decompression recovers every element of the displayed image. Multiplication
is preserved by the same identity. Hence the two algebras are isomorphic and
their complete semisimple representation tables agree. The matrix-prefix
formula `(PTS3)` follows from the cited head-amplification theorem and does
not alter this type identity.
