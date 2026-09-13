---
rg: 2
id: labbe-not-fp-via-infinitely-generated-homology
kind: route
title: DEAD - refute finite presentation of Labbé's derived full group through infinitely generated integral homology
target: labbe-shift-derived-full-group-is-not-finitely-presented
requires: []
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-labbe-2026-09-13.md
---

**Dead route.** It is invalidated by `labbe-shift-derived-full-group-homology-is-finitely-generated`, which is
established.

**Intended argument.** A finitely presented group has finitely generated `H_2`. By Li's theorem,
`H_2(D(G))` is `π_2` of the groupoid K-theory spectrum. It is infinitely generated as soon as
`H^1(Z^2; C(Omega_U, Z/2))` or `H^2(Z^2; C(Omega_U, Z/2))` is infinite
(`z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite`).

**Why it dies.** Labbé's morphism is expansive and recognizable. So both groups are finite, with
at most `2^{N_{3,3}}` and `2^{N_{4,3}+N_{3,4}}` elements
(`recognizable-self-similar-z2-subshifts-have-finite-cohomology`).
- In degree 2, `H_2(Gamma) ≅ Z ⊕ (finite 2-group)`.
- Every `π_j`, `j >= 2`, of the universal cover is finitely generated, so all `H_j(Gamma)` are.
