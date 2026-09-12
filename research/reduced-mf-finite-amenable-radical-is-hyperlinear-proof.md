---
rg: 2
id: reduced-mf-finite-amenable-radical-is-hyperlinear-proof
kind: route
title: Visibility off the radical, visibility inside a finite normal radical, then elementwise
target: reduced-mf-finite-amenable-radical-is-hyperlinear
requires: [reduced-mf-hyperlinear-radical-in-amenable-radical, mf-finite-normal-tracially-visible, hyperlinear-elementwise-visibility]
---

Let `iota : C*_r(G) -> Q` be an MF embedding.

1. **`G` is operator MF.**  `g -> iota(lambda_g)` is a homomorphism into
   `U(Q)`, injective because `lambda` is faithful and `iota` is injective.
2. **Outside the radical.**  Every `g notin R_a(G)` is tracially visible by
   `reduced-mf-hyperlinear-radical-in-amenable-radical`.
3. **Inside the radical.**  `R_a(G)` is a normal subgroup, finite by
   hypothesis.  By step 1 and `mf-finite-normal-tracially-visible`, every
   `g != 1` in it is tracially visible, with constant at least
   `c(R_a(G)) / |R_a(G)|`.
4. **Conclusion.**  Every nontrivial element is tracially visible, so `G` is
   hyperlinear by `hyperlinear-elementwise-visibility`.
