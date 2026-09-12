---
rg: 2
id: density-random-group-positive-b2-proof
kind: route
title: Intersect the asphericity and property (T) events and read b_2 off the Euler characteristic
target: density-random-group-hyperbolic-kazhdan-with-positive-b2
requires: [gromov-density-random-groups-hyperbolic-aspherical, gromov-density-random-groups-kazhdan-above-third]
artifacts:
  - research/artifacts/density-random-groups-b2-verified-2026-09-12.md
---

Fix `m >= 2`, `d ∈ (1/3, 1/2)`, and let `ℓ → ∞` through multiples of 3.

1. **Models.** `gromov-density-random-groups-hyperbolic-aspherical` uses a
   uniform *set* of relators. `gromov-density-random-groups-kazhdan-above-third`
   uses independent uniform choices, which may repeat. The expected number of
   coincident pairs is at most `(2m−1)^{2dℓ}` divided by the number of
   cyclically reduced words of length `ℓ`, which tends to 0 because `d < 1/2`.
   Conditioned on having no repeats, the multiset model is the set model, and
   the group does not depend on repeated relators. So any w.o.p. property of the
   group in one model is w.o.p. in the other.
2. **Intersection.** The intersection of two w.o.p. events is w.o.p. So w.o.p.
   `G` is infinite hyperbolic, the presentation complex `X` (one vertex, `m`
   edges, `|R|` faces) is aspherical, and `G` has property (T). Asphericity
   gives `cd(G) <= 2` and torsion-freeness, as recorded in the first premise.
3. **Betti number.** `X` is a finite `K(G,1)`, so the rational Betti numbers of
   `G` are those of `X`, and
   `1 − m + |R| = χ(X) = b_0 − b_1 + b_2 = 1 − b_1(G) + b_2(G)`.
   Property (T) forces `H^1(G; R) = 0`, hence `b_1(G) = 0`, so
   `b_2(G) = |R| − m = ⌊(2m−1)^{dℓ}⌋ − m`. Since `d > 1/3`, for `ℓ >= 6` this
   is at least `(2m−1)^2 − m − 1 >= 4 >= 1`.
