---
rg: 2
id: literal-structure-from-block-amalgam
kind: route
title: Assemble the literal structure question from the block amalgam
target: literal-group-structural-normal-form
requires: [literal-telescope-split-normal-form, literal-lamp-kernel-clifford-block-amalgam, literal-witness-kernel-free, literal-word-problem-solvable]
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

## Why sufficient

The root asks for three things.  The normal form is the unique decomposition
`p g` of `literal-telescope-split-normal-form` together with the amalgamated
normal form for `p` supplied by `literal-lamp-kernel-clifford-block-amalgam`.
The kernel of the witness map is computed exactly by
`literal-witness-kernel-free`: it is free of countably infinite rank, so `E` is
free-by-sofic.  The word problem is `literal-word-problem-solvable`.  Together
these give the requested usable description:

    E = (*_{<w>} ClLamp(8)) semidirect_product V,
    V = (Z[1/2]^3 x| SL_3(Z)) x| Z <= GL_4(Q),
    W = the quotient collapsing the block structure to "all sites anticommute".
