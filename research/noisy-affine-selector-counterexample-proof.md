---
rg: 2
id: noisy-affine-selector-counterexample-proof
kind: route
title: Recover the planted pairing direction by concentration and choose triangle edges
target: noisy-affine-selector-defeats-bounded-hitting
requires: []
artifacts:
  - research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md
  - scripts/check_unique_games_noisy_direction.py
  - research/artifacts/unique-games-noisy-direction-replay-2026-09-07.json
---

Sections 1--4 of the artifact give the full proof. For a uniformly random
point in `D_b` followed by ambient `rho`-noise, the true pair score has
mean `rho^2`, while each wrong score is an average of independent,
mean-zero four-point blocks. Bounded-variable concentration and a union
bound give decoder error at most `(N-1)exp(-N rho^4/32)`, uniformly in `b`.
This makes the selected quotient singleton coefficient at least `rho/2`
for sufficiently large `N`.

The bijections `J` and `J^2=J+I` make each nonzero label belong to exactly
two selected cosets. Their order-three orbits form disjoint triangles,
giving both the hitting bound and the exact pair-star density. The artifact
derives the concentration inequality, fixes the quantifier order, treats
ties, and supplies an explicit threshold at `rho=1/2`.

This direct-proof route establishes the counterexample only. It has no
hardness conclusion. The Python replay supplies finite checks in addition
to the mathematical proof; Cairn checks dependencies, not the proof itself.
