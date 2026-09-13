---
rg: 2
id: penrose-not-fp-via-infinitely-generated-homology
kind: route
title: DEAD - refute finite presentation of the Penrose derived full group through infinitely generated integral homology
target: penrose-derived-full-group-is-not-finitely-presented
requires: []
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**Dead route.** It is invalidated by `penrose-derived-full-group-homology-is-finitely-generated`, which is
established.

**Intended argument.** A finitely presented group has finitely generated `H_2`. So an infinitely
generated `H_2(D(𝒫); Z)` would refute finite presentation. Through Li's theorem, `H_2(D(G))` is
`π_2` of the groupoid K-theory spectrum
(`derived-full-group-h2-filtered-by-mod-two-groupoid-homology`). It is infinitely generated as
soon as `H_0(G; Z/2)` or `H_1(G; Z/2)` is infinite.

**Why it dies.** For the Penrose tiling groupoid these are `(Z/2)^8` and `(Z/2)^5`. So
`H_2(D(𝒫)) ≅ Z ⊕ T` with `T` of order `2^12` or `2^13`. Every `H_j(D(𝒫))` is finitely
generated, so no degree helps.
