---
rg: 2
id: recognizable-self-similar-z2-subshifts-have-finite-cohomology
kind: claim
title: Recognizable self-similar Z^2-subshifts have finite cohomology with finite coefficients in degrees one and two, bounded by pattern counts
distinct_from:
  z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite: That is the criterion turning finiteness of H^1 and H^2 with Z/2 coefficients into finite generation of H_2 of the derived full group; this proves that finiteness for every self-similar subshift with a recognizable expansive morphism.
  labbe-shift-derived-full-group-escapes-known-obstructions: That checks recorded dynamical obstructions against Labbé's shift; this is a cohomology bound for all recognizable self-similar Z^2-subshifts.
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-labbe-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.** Labbé, arXiv:1802.03265, lines 813–823, 884, 1012–1016 and 1134–1143.
- `X ⊆ A^{Z^2}` is a subshift and `ω : X -> X` is a 2-dimensional morphism.
- `ω` is expansive: every shape of `ω^m(a)` grows without bound.
- `ω` is recognizable in `X`: each point has at most one centered `ω`-representation.
- `X = closure_σ(ω(X))`.
- `N_{a,b}` is the number of `a × b` patterns occurring in `X`.

**Theorem 6.** For every `m >= 2`:
- `|H^2(Z^2; C(X, Z/m))| <= m^{N_{3,3}}`;
- `|H^1(Z^2; C(X, Z/m))| <= m^{N_{4,3} + N_{3,4}}`.

In particular, with `m = 2`, both groups are finite. Primitivity is not needed.
- **Integral coefficients.** `H^2(Z^2; C(X, Z))` is finitely generated.
- Integral `H^1` need not be: it can be an increasing union of bounded-rank groups, as `Z[1/2]` is.

**Method.**
- Recognizability makes the level-`n` supertile decomposition continuous, and the supertiles
  form a grid.
- In degree 2, every coinvariant class is a sum of classes of indicators of supertile corners of
  a given collared type.
- In degree 1, a cocycle minus the potential integrated inside each supertile is supported on
  supertile boundaries. It is constant along each boundary and depends only on the adjacency
  block.
- The number of collared types at level `n` equals the number at level 0.

Proof: `recognizable-self-similar-z2-cohomology-proof`.
