---
rg: 2
id: weak-sofic-surjunctivity-from-metric-ultraproducts
kind: route
title: Embed a weakly sofic group in a metric ultraproduct and pass surjunctivity to the subgroup
target: weakly-sofic-groups-are-surjunctive
requires:
  - metric-ultraproducts-of-finite-groups-are-surjunctive
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Let `G` be countable and weakly sofic.

- **Embedding.** Exhaust `G` by finite sets `F_n` and choose models
  `(H_n, l_n, phi_n)` with defects `eps_n -> 0` and separation `c_n` on `F_n`.
  The rescaled length `min(1, l_n / c_n)` is again an invariant length, and it
  pushes separation to `1` while scaling the defect by `1/c_n`. So one may assume
  `c_n = 1` and `eps_n -> 0`.
- `g -> (phi_n(g))_n` gives a homomorphism `G -> Q = prod H_n / N_omega`, because
  the defects tend to `0`. It is injective because separations stay equal to `1`.
- The prerequisite makes `Q` surjunctive, and `surjunctivity-passes-to-subgroups`
  passes it to `G`.

This route and `metric-ultraproduct-surjunctivity-from-weak-sofic-case` form an
intended equivalence cycle, so neither establishes its target alone.

**Verification.** `w3-vf-positive` passed this route (Section 3.4 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
