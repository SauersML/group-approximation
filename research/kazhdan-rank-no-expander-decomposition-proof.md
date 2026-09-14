---
rg: 2
id: kazhdan-rank-no-expander-decomposition-proof
kind: route
title: Truncate field degrees in the natural representations of EL_3(F_2[t]) over finite fields
target: kazhdan-group-rank-models-admit-no-expander-decomposition
requires:
  - elementary-group-property-t-over-free-algebras
artifacts:
  - research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md
---

## Why sufficient

`elementary-group-property-t-over-free-algebras` makes `{ e_ij(1), e_ij(t) }` a Kazhdan
set for `EL_3(F_2[t])`, since `F_2[t]` is the free algebra on one generator. The rest is
linear algebra, in Sections 1-3 of the artifact.

* **Irreducible.** `SL_3(F_q)` is transitive on nonzero vectors.
* **Almost invariant.** `rho_k(e_ij(t)) = 1 + E_ij (x) C`, where `C` is multiplication by
  `alpha`. The truncations `pi_m` satisfy `rank[pi_m, C] <= 2`, and `W_m n e_ij(t) W_m`
  has codimension at most `1` in `W_m`.
* **Boundaries of intersections.** `b(X n Y) <= b(X) + b(Y)`.
* **Decompositions.** A proper nonzero piece `P` has `b(P) >= 1`, by irreducibility. The
  subspaces `P n W_m` grow in steps of dimension at most `3`, so one has about half the
  dimension of `P` and boundary at most `b(P) + 6`. Internal `kappa`-expansion then
  forces `dim P < 20 b(P)/kappa`.
* **Perturbed models.** A rank perturbation of the generators by `delta n` changes each
  `e_s` by at most `delta n`.
