---
rg: 2
id: low-rank-full-square-zero-forces-doubled-line
kind: claim
title: In rank two or three a full square-zero section splits off a doubled line bundle
distinct_from:
  homogeneous-full-square-zero-is-nilpotent-section: that identifies fullness with pointwise nonvanishing in every rank; this computes the resulting topological condition exactly when the rank is at most three.
---

**ESTABLISHED.**  Let `E` be a complex vector bundle over a compact Hausdorff
space `X`.

1. If `E ~= L directSum L directSum M` for a line bundle `L` and some bundle
   `M` (possibly zero), then `Gamma(X, End E)` contains a full square-zero
   element.
2. If `rank E` is `2` or `3`, the converse holds: a full square-zero element
   forces `E ~= L directSum L directSum M` with `L` a line bundle and
   `rank M=rank E-2`.

**Examples with no full square-zero element.**

- `X=S^4`, `E` the quaternionic Hopf bundle regarded as a complex rank-two
  bundle, with `c_2(E)` a generator of `H^4(S^4; Z)`.
- `X=S^6`, `E=TS^6` with its octonionic almost complex structure, a complex
  rank-three bundle with `c_3(E)=e(TS^6)=2` times a generator.

In both cases `H^2(X; Z)=0`, so every line bundle is trivial, and
`L directSum L directSum M` would be trivial, contradicting the nonzero top
Chern class.

These algebras have finite-dimensional representations, so they are not
LXXIII examples.  They record the base case of the stage obstruction: the
nilpotent-section bundle `N_0(E)` can have no section, detected by ordinary
characteristic classes, as long as every nonzero square-zero fibre element has
rank one.
