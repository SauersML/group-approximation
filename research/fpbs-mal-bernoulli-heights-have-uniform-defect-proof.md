---
rg: 2
id: fpbs-mal-bernoulli-heights-have-uniform-defect-proof
kind: route
title: Read the height as a graph vector, split off its l^2(Y) mean, and apply the Kesten gap of the regular representation absorbed by Fell
target: fpbs-mal-bernoulli-heights-have-uniform-defect
requires: []
artifacts:
  - research/artifacts/fpbs-mal-bernoulli-height-defect-2026-09-20.md
---

The full proof is §2 of the artifact.

1. **Koopman.** Every stage `H_n` is torsion-free, so it acts freely on
   the tensor basis of `L^2_0([0,1]^Gamma)`. Hence `kappa_0|H_n` is a
   multiple of `lambda_{H_n}`.
2. **Fell absorption.** `lambda ⊗ pi ≅ (dim pi) lambda`, through
   `delta_h ⊗ v -> delta_h ⊗ pi(h)^{-1} v`. So
   `L^2_0(X) ⊗ l^2(Y)` is a multiple of `lambda_{H_n}`.
3. **Kesten.** H. Kesten, *Symmetric random walks on groups*, Trans. AMS 92
   (1959): simple random walk on the rank-2 free group has spectral radius
   `sqrt 3/2`. So
   `sum_{s in {a, b_n}} ||s v - v||^2 >= (4 - 2 sqrt 3)||v||^2` on every
   multiple of `lambda`.
4. **Graph vector.** `xi = 1[f(x) = y]` in `L^2(X x Y)` has
   `||s xi - xi||^2 = 2 d_s(f)`. Its component orthogonal to `l^2(Y)` has
   squared norm `1 - sum p_y^2`. Apply 3 to that component. This is item 1.
5. **Concentration.** If `s` has no fixed point on `Y`, then
   `d_s >= 2 p* - 1`, with `p* = max p_y >= sum p_y^2`. Balancing this
   against item 1 gives `kappa = (2 - sqrt 3)/(4 - sqrt 3)`. This is item 2.
