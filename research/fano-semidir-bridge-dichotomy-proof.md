---
rg: 2
id: fano-semidir-bridge-dichotomy-proof
kind: route
title: Separate Pauli and actor quotient support for every finite Fano bridge word
target: fano-semidir-bridges-are-wrong-subgroup-or-gauged
requires:
  - el20-order-seven-heads-force-zero-common-hecke-reducing-cut
  - fano-moving-packet-retains-actor-holonomy
---

The actor matrices and the directed list `(FSD3)` are the explicit block
calculation in the required zero-cut claim.  On `(4,7,8)`, the first Singer
matrix sends `e_8^*` to `e_7^*`; conjugating the rank-one transvection proves
`(FSD2)`.  Since no generator in `(FSD3)` uses `7` as a source, all of
`L_0` fixes `e_7`, proving `(FSD4)`.

The quotient map `A semidirect K -> K` is unchanged by conjugation with an
element of `A`.  Hence the Fourier support of an `L_0` Reynolds projection
still projects to `L_0` after every pure coefficient conjugation, and cannot
equal the Reynolds projection over `tL_0t^(-1)`.  In the complementary case,
the regular-amplified exact representation `(FSD5)` from the moving-holonomy
fence assigns the bridge its nontrivial actor gauge.  This proves the two
branches.
