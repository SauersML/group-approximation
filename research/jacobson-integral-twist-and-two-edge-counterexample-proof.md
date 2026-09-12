---
rg: 2
id: jacobson-integral-twist-and-two-edge-counterexample-proof
kind: route
title: Twist one finite packet by commuting translations and test the shared finite identity
target: jacobson-third-packet-correction-must-move-an-edge
requires:
  - jacobson-coherent-quotient-has-four-word-gap-criterion
  - jacobson-shift-literal-quotient-is-laurent-times-z
  - jacobson-coherence-defect-is-an-orthogonal-translation
artifacts:
  - research/artifacts/jacobson-third-packet-cannot-be-corrected-with-both-edges-fixed-2026-09-08.md
---

The far-coordinate actions authenticate both full intersections. On
the integral permutation module of the seven nonzero binary vectors,
conjugate the second finite factor by the basis vector at `e_2`.
The common subgroup fixes that vector, both mixed relators hold, and
the coherence word is the difference of two distinct basis vectors.
This proves its infinite order and the integral quotient assertion.

Represent the same module using commuting translation involutions on
eight points and exponentiate with parameter `theta`. The word has
eigenvalues `1,exp(2i theta),exp(-2i theta)` while every old relator
is exact. Use the twisted representation on `A` and the untwisted
one off `A`; the resulting complete approximate table is within
`2 sin(theta)` of an exact table and has defect at most `6 sin(theta)`.
Preserving both edge restrictions would force the displayed nonidentity
word to equal identity. Six-letter telescoping gives the necessary
movement inequality. None of these models retains the original head.
