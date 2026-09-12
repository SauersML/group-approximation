---
rg: 2
id: clifford-cover-center-separable-pullback-proof
kind: route
title: A finite quotient keeping the center is a finite Clifford group over a quotient site set, and conversely
target: clifford-cover-center-separable-iff-graph-is-finite-pullback
requires: []
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Artifact Section 1, Theorem A.

- **If.** Map `c_x` to `c_(Kx)` in the finite Clifford group over `K\X` with the quotient graph, and `g` to
  `gK`. Every defining relation of `E_S` is preserved, because the graph is pulled back and fibres carry no
  edge. So `eps` maps to the nontrivial central involution.
- **Only if.** Given `f` with `f(eps) != 1`, the images `f(c_x)` form a finite `G`-set under conjugation.
  Adjacency is exactly non-commutation of images. The kernel `K` of the permutation action makes the site
  map factor through `K\X`.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including both corollaries:
the `L`-bi-invariance criterion, infinite degree from `[L : Gamma] = infinity`, and the complete-graph case
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 7.1).
