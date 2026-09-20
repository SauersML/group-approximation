---
rg: 2
id: boundedly-controlled-torus-rank-loss-proof
kind: route
title: Relative cup length on a fibre neighbourhood of the row characters, averaged over random private output sets
target: boundedly-controlled-torus-maps-lose-rank-linearly-in-surplus
requires: []
artifacts:
  - research/artifacts/controlled-torus-rank-cup-length-2026-09-20.md
---

The complete proof is in the artifact, Sections 0 to 5. Section 6 gives checks and consequences.
1. Lemma N gives coarse inverses.
2. Coordinates are adapted to a private output set `T`.
3. Lemma F gives real lifts on a fibre neighbourhood `N_0`, and Lemma S' gives the localised slice
   lemma.
4. Lemma C: `dim_W(X_T) <= D - delta(T)`. It uses an Ostrand cover of the `Z`-projection polyhedron
   and `r` arc sets for the row classes, then the relative cup product.
5. Averaging over random `T` with density `p` gives `L h_K(p) <= D`.
