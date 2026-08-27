---
rg: 2
id: literal-lamp-kernel-clifford-block-amalgam
kind: claim
title: The literal lamp kernel is a central amalgam of order-512 Clifford blocks
distinct_from:
  literal-telescope-split-normal-form: That claim gives the splitting and identifies the quotient `V`; this one identifies the isomorphism type of the lamp kernel and the orbital block structure.
  finite-site-orbits-invariant-clifford-kernel: That established claim is a general finite-orbit criterion producing finite invariant subgroups; this one computes the concrete literal lamp group, which is infinite and contains free subgroups.
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - non_mf_groups_exist.tex
---

Coordinatize the site set of the literal group as
`X = V/B = disjoint_union_{n in Z} Z[1/2]^3 / 2^n Z^3`, the class of
`t tau^n B` being `(n, [u] mod 2^n Z^3)`.  The `V`-orbit of the marked pair
`{tau o, v_1 tau o} = {(1,[0]), (1,[e_1])}` is the edge set of a 7-regular
graph whose connected components ("blocks") are the cosets of
`2^(n-1) Z^3 / 2^n Z^3`, each a complete graph on eight sites; the block set is
`V`-isomorphic to `X` itself, with block stabilizers the telescope levels.

Consequently the lamp kernel of the literal group is

    N_E = free product over i in I of ClLamp(8), amalgamated over the common
          central involution <w> = Z/2,

with `I` countably infinite, each block group of order `2^9 = 512`, and

    E = (V x <w>) *_{B_1 x <w>} (ClLamp(8) semidirect_product B_1),
    E/<w> = (*_{i in I} (Z/2)^8) semidirect_product V,

where `B_1` is the level containing `B` with index eight and acts on the eight
block sites through the finite affine group `AGL_3(F_2)`.
