---
rg: 2
id: literal-witness-kernel-free-proof
kind: route
title: Free action on the block tree computes the witness kernel
target: literal-witness-kernel-free
requires: [literal-lamp-kernel-clifford-block-amalgam]
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

## Direct proof

Section 6 of the artifact.  The witness map induces the identity on the
telescope quotients and carries the lamp kernel onto `ClLamp(X)`, so its kernel
is `ker(N_E -> ClLamp(X))`.  In the amalgam
`N_E = *_{<w>} ClLamp(8)` every block maps isomorphically onto the Clifford
lamp group of its eight sites and `w` maps to the nontrivial sign, so the
kernel, being normal, meets every conjugate of every vertex group trivially.
A group acting on a tree with trivial vertex stabilizers is free (Serre).

Nonabelian: three sites in three different blocks generate
`Z/2 * Z/2 * Z/2` by the amalgam normal form, its index-two subgroup is free of
rank two, and its image in the locally finite group `ClLamp(X)` is finite, so
the intersection with the kernel is a finite-index, hence nonabelian free,
subgroup.  Infinite rank: a finitely generated subgroup of the amalgam lies in
the sub-amalgam of finitely many blocks, while `[c_x,c_y] w` for `y` outside
that finite set of blocks lies in the kernel and outside the sub-amalgam.
Nonabelian free groups are not amenable.
