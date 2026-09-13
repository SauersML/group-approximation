---
rg: 2
id: every-braid-group-is-cat0
kind: claim
title: Every braid group acts geometrically on a complete CAT(0) space
distinct_from:
  every-braid-group-acts-properly-on-a-proper-cat0-space: that claim drops cocompactness and asks only for a proper isometric action on a proper CAT(0) space; this one asks for a geometric action, the standard meaning of a CAT(0) group
---

For every `n >= 1` there is a complete CAT(0) metric space `X_n` on which the
braid group `B_n` acts properly and cocompactly by isometries. This is the
affirmative answer to Zaremsky Problem 3.6
(`zaremsky-3-06-braid-groups-cat0`).

Calibration: `B_1` is trivial and `B_2 = Z` acts on the line. `B_3` acts
geometrically on a tree times a line.

## Attempts

- **Orthoscheme route (Brady–McCammond).** The dual Garside structure of
  `B_n` (T. Brady) gives a compact `K(B_n, 1)` whose cells come from chains in
  the noncrossing-partition lattice `NC_n`. With the orthoscheme metric of
  Brady–McCammond (arXiv:0909.4778), `B_n` is CAT(0) as soon as this complex
  satisfies the link condition. Per the abstracts: Brady–McCammond settle
  rank 4 (`n = 5`); Haettel–Kielak–Schwer (arXiv:1304.5990) prove "braid
  groups with at most 6 strands are CAT(0)" by embedding diagonal links into
  spherical buildings of type A, and also that orthoscheme complexes of bounded
  graded modular complemented lattices are CAT(0); Jeong (arXiv:2009.09350)
  proves `B_7` is CAT(0) by elaborating the same argument. Open for `n >= 8`.
  The lane is reading both papers to find exactly which step needs `n <= 7`.
- **Lattice-theoretic versions.** Chalopin–Chepoi–Hirai–Osajda
  (arXiv:1409.3892) and Hirai (arXiv:1905.01449) prove CAT(0) orthoscheme
  complexes for modular lattices and modular semilattices. `NC_n` is not
  modular, so these do not apply directly. A convexity statement for `NC_n`
  inside a modular lattice containing it would be enough.
- **Things that do not block the route (sources to verify).** The standard
  consequences of CAT(0) hold for `B_n`: finite presentation, undistorted
  cyclic subgroups (finite-type Artin groups are biautomatic), solvable
  subgroups virtually abelian, and a virtually split center (the pure braid
  group is `Z x P_n/Z(P_n)`). Haettel (arXiv:1509.08711) rules out cubical
  models for `n >= 4`, so the model has to be genuinely non-cubical.
