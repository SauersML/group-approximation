---
rg: 2
id: robertson-steger-no-spatial-realization-via-rigidity
kind: route
title: Cocycle rigidity puts every letter-count class in the degree plane, which the Bernoulli pinning theorem forbids
target: robertson-steger-tile-groupoids-have-no-spatial-realization
requires:
  - spatial-two-graph-realizations-in-g2n-leave-the-degree-plane
  - robertson-steger-two-graph-groupoids-are-cocycle-rigid
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
---

Details: Corollary 3.2 and Section 5 of the artifact.

1. **Hypotheses of the theorem.**
   - `Λ_T` is finite.
   - "No sources" and `ρ(M_1) > 1` are part (b) of `robertson-steger-two-graph-groupoids-are-cocycle-rigid`.
     It is checked exactly for `q = 2, 3` (primitive, row sums `q^2`) in
     `cmsz-pg22-no-brick-coding-certificate` and `cmsz-pg23-no-brick-coding-by-kraft`.
2. **Rigidity.** By `robertson-steger-two-graph-groupoids-are-cocycle-rigid`, each locally
   constant cocycle `N^ε_i∘ι` is cohomologous to some `a d_1 + b d_2`.
3. **Contradiction.** This contradicts
   `spatial-two-graph-realizations-in-g2n-leave-the-degree-plane` (i).
