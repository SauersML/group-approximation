---
rg: 2
id: leavitt-path-unit-groups-l2-acyclic-proof
kind: route
title: Cancellation turns simultaneous strong division into frame extension, then the frame criterion
target: leavitt-path-unit-groups-with-trivial-unit-class-are-l2-acyclic
requires: [frame-acyclic-rings-have-low-degree-l2-acyclic-gl, leavitt-path-algebras-have-simultaneous-strong-division, purely-infinite-leavitt-path-v-monoid-cancellation, leavitt-path-algebras-purely-infinite-simple-criterion]
artifacts:
  - research/artifacts/leavitt-path-unit-l2-acyclicity-2026-09-12.md
---

Artifact Sections 2--4.
- **Pure infiniteness and the Leavitt family.** `L_K(E)` is purely infinite simple (Abrams--Aranda
  Pino Theorem 11). Cancellation makes `[1] = 0` give `L ≅ L²`, a unital Leavitt family
  `e_i f_j = δ_ij`, and `GL_r(L) ≅ L^x`.
- **Division with nonzero kernels.** Simultaneous strong division gives `u_i a_i X = 1`. Replacing
  `X` by `X f_0` and `u_i` by `e_0 u_i` keeps the identity and puts `f_1 != 0` in every kernel.
  Every kernel has class `0`, so it is `≅ L^(q-1)`.
- **Frame connectivity.** Khanh's Proposition 4.2 and his coning Corollary 4.3 then hold for
  `X_r(L)`.
- **Conclusion.** The frame criterion at `r = n+3` gives L²-acyclicity in degree `n`.
