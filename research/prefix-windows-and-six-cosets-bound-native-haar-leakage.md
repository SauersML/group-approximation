---
rg: 2
id: prefix-windows-and-six-cosets-bound-native-haar-leakage
kind: route
title: Refine the backward lamps to finite prefix charts and count six disjoint cosets
target: native-backward-lamp-algebras-have-fixed-forward-leakage
requires:
  - native-s3-algebra-enlargement-obstructs-scalar-commutants
artifacts:
  - research/artifacts/leavitt-backward-lamp-windows-and-canonical-haar-obstruction-2026-09-08.md
---

Conjugation by `u^(-1)` on `K` is the injective corner embedding
`k -> 1+s^3(k-1)t^3`. Its backward lamps interchange elementary
module coordinates indexed by `0^j3` and `0^(j+1)` in the four-letter
prefix alphabet `{000,001,01,1}`. Both coordinates have the same
four-letter length. Refining them to length `m+1` puts all lamps in
one finite constant matrix group. The charts embed by `A -> A tensor I_4`.

For finite subgroups `G,T`, canonical Fourier projections onto
their complex group algebras overlap in exactly `|G intersect T|`
dimensions. The Haar covariance of the regular-trace algebra
`C[G]` is its Hilbert-space projection divided by `|G|`, giving
the exact leakage `1-|G intersect T|/|G|`.

The conjugated finite subgroup `uF_0u^(-1)` is an explicit `S_3`
on the first-coordinate `e` corner and coordinate four. Its
intersection with `K` is trivial. Therefore it supplies six distinct
cosets of `G_m intersect uG_m u^(-1)` in `uG_m u^(-1)`, proving
the uniform `5/6` lower bound.

The artifact also proves the amenable ascending-union structure and
the fixed-stage matrix transfer by finite Gram-matrix continuity.
Its diagonal statement requires windows to grow slowly enough for
those finite-stage estimates. It makes no unproved approximation
uniform over all word lengths or all growing windows.
