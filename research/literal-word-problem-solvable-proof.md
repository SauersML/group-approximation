---
rg: 2
id: literal-word-problem-solvable-proof
kind: route
title: Decide triviality by telescope matrices plus block-amalgam reduction
target: literal-word-problem-solvable
requires: [literal-telescope-split-normal-form, literal-lamp-kernel-clifford-block-amalgam]
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

## Direct proof

Section 7 of the artifact.  The split structure gives the unique
decomposition `p g` with `g` in the linear group `V <= GL_4(Q)`, computable by
matrix multiplication with the stable-letter exponent recorded by the
determinant; triviality there is decidable.  The block coordinates of
Proposition 4.1-4.2 make site equality and same-block membership decidable
rational tests.  The amalgamated normal form theorem for a family of finite
groups amalgamated over a common central subgroup makes the greedy reduction
of the lamp word (multiply consecutive same-block letters inside the
order-512 group, delete central results after moving the sign to the front)
terminate in a normal form that is trivial exactly when the element is
trivial.
