---
rg: 2
id: arithmetic-star-packet-carrier-proof
kind: route
title: Attach S9 to the eight affine cosets and preserve the moved star transposition in the amalgam
target: arithmetic-star-packet-carrier
requires:
  - affine-congruence-source-is-kazhdan
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

Cairn's affine source gives a finitely presented `P`, an injective doubling
map with index-eight image `H`, and `p_0 notin H`.  Coset action makes `H`
the stabilizer of the base point, so it fixes `k=(H star)`, while `p_0`
sends `k` to `(p_0 H star)`.  Factor injectivity for the amalgam preserves
the resulting nontrivial commutator.

Finite presentation follows from finite presentations of `P`, its ascending
HNN extension, and the finite-by-`P` packet host, followed by finitely many
identifications of generators of the amalgamated copy of `P`.

Translations reduce onto `F_2^3`.  The matrices `e_ij(3)` belong to
`Gamma(3)` and reduce to `e_ij(1)` modulo two; these generate
`SL_3(F_2)=GL_3(F_2)`.  Hence the two permutation images are
`AGL(3,2)` and `GL(3,2)`.

