---
rg: 2
id: pure-braided-bht-braid-characters-dimension-n-n-minus-1-proof
kind: route
title: "Solve the splitting relations on orbit types of leaf pairs"
target: pure-braided-bht-braid-characters-dimension-n-n-minus-1
requires: []
artifacts:
  - research/artifacts/zp-pure-braided-bht-characters-2026-09-13.md
---

Direct proof, written out in the artifact (§§1–4):

- Lemma 1: residue mod `d` of `n`-adic numbers is additive and invariant
  under PL maps with slopes in `<n>`.
- Lemma 2: two positive gaps can be matched by such a map iff residues agree
  (subdivide into standard intervals; counts are congruent mod `d` and can be
  raised by `d`).
- Lemma 3: orbits of leaf pairs = types.
- `H_1(N)` is the colimit of `H_1(PB_k)` under cabling, which sends
  `A_{ij}` to the sum over the cable. Conjugation by `F_{n,r}` relabels leaves.
  So `W` = type functions satisfying the two splitting relations RI and RJ.
- Theorem 1: RI and RJ reduce to zero row sums and zero antidiagonal sums on the
  interior array (rank `2d - 1` by Fourier analysis on `(Z/d)^2`), zero sums on
  the first-leaf and last-leaf families, and three derived boundary values.
  Count `(d-1)^2 + 2(d-1) + d + 1 = n(n-1)`.
- Proposition 2: cabling a full twist gives the full twist on more strands
  times the inverse internal twist of the cable, so `tau(k + d) - tau(k)` is
  constant for `k >= 3`. `EPE = 1` and `PEP ≡ 1` show the map to affine
  functions is onto.
