---
rg: 2
id: labbe-matricial-via-scale-one-torus-module
kind: route
title: One nonzero finite-dimensional module of a scale-1 Labbé torus tiling algebra over F_q makes the Labbé crossed product exactly matricial
target: labbe-wang-shift-crossed-product-is-exactly-matricial
requires:
  - labbe-ring-matricial-iff-scale-one-torus-module
  - labbe-torus-tiling-algebra-has-scale-one-module
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
---

The (⇐) direction of `labbe-ring-matricial-iff-scale-one-torus-module` (artifact §6, Theorems B–C), applied to the
module supplied by `labbe-torus-tiling-algebra-has-scale-one-module`:
1. induce a covariant `1`-family;
2. double its scale along the tower of `ω^2`;
3. restrict to period tori over `F_q`;
4. descend to every scale;
5. apply the torus criterion. ∎
