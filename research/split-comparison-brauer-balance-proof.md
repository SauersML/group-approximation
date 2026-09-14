---
rg: 2
id: split-comparison-brauer-balance-proof
kind: route
title: Take conditional expectation onto the actor group, push to the finite image, and compare induced Brauer characters
target: split-comparisons-balance-induced-brauer-characters
requires: []
artifacts:
  - research/artifacts/kaplansky-torus-fusion-brauer-balance-2026-09-11.md
---

Complete direct proof; Section 1 of the artifact gives every step.

1. The coefficient restriction `E_H : F_p[G] -> F_p[H]` is an `F_p[H]`-bimodule
   map. Since `Z` and `f` lie in `F_p[H]`, `E_H(L) Z = f`, and
   `f E_H(L) e` is a left inverse of `Z` inside `f F_p[H] e`.
2. Push forward along `pi`. `q = Zbar Lbar` is an idempotent below `ebar`, and
   left multiplication by `Zbar` is an isomorphism `fbar F_p[F] -> q F_p[F]`.
3. Injectivity of `pi` on `K` makes `F_p[F]` free over `F_p[pi K]`, so
   `ebar F_p[F]` and `fbar F_p[F]` are the induced modules, of dimensions
   `[F : pi K]` times the chart ranks.
4. Equal chart ranks force `q F_p[F] = ebar F_p[F]`, hence `q = ebar`: the
   induced modules are isomorphic.
5. Isomorphic modules have equal Brauer characters. The Brauer character of an
   induced module is the induced class function; evaluating it at `x` and
   dividing by `|C_F(x)|` gives the displayed balance.
