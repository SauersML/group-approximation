---
rg: 2
id: complete-overlay-code-conjugation-gap-proof
kind: route
title: Decompose matrix space by pairs of code characters
target: complete-overlay-code-group-has-uniform-conjugation-gap
requires:
  - quadratic-repetition-supports-complete-commutation-overlay
---

The complete overlay makes the group finite abelian.  Decompose every
representation into its character spaces and then decompose Hilbert-Schmidt
matrix space into ordered character blocks.  On an off-diagonal block, the
coordinate conjugation signs form the nonzero difference codeword, so code
distance moves that block on at least `delta L` generators.  The diagonal
equal-character blocks are precisely the commutant.
