---
rg: 2
id: literal-word-problem-solvable
kind: claim
title: The literal forty-one-relator presentation has solvable word problem
distinct_from:
  literal-telescope-split-normal-form: That claim records the split structure and the identification of the telescope quotient; this one records the resulting decision procedure.
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

There is an algorithm deciding whether a word in the eight literal generators
is trivial in `E`.  Push the lamp letters left, recording each as a site of
`X = disjoint_union_n Z[1/2]^3/2^n Z^3` computed by rational matrix arithmetic
in `GL_4(Q)`; site equality and block membership are finite rational tests.
Reduce the resulting lamp word inside the block amalgam by multiplying maximal
same-block runs in the explicit group of order 512 and moving the central sign
to the front.  The word is trivial iff the telescope part is the identity
matrix with zero stable-letter exponent and the reduced lamp word is empty
with trivial sign.

So the literal group has solvable word problem although it is neither
residually finite nor MF: the Theorem A obstruction is analytic, not
algorithmic.
