---
rg: 2
id: metric-ultraproduct-surjunctivity-from-weak-sofic-case
kind: route
title: Localize a strict automaton over a metric ultraproduct to its countable memory group, which is weakly sofic
target: metric-ultraproducts-of-finite-groups-are-surjunctive
requires:
  - weakly-sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

- **Localization.** Let `tau` be a strict automaton over `Q` with memory `M`. By
  the coset transfer of `surjunctivity-passes-to-subgroups`, injectivity and
  surjectivity transfer both ways between `Q` and `<M>`, so `tau` is strict over
  the countable group `<M>`.
- **`<M>` is weakly sofic.** For a finite `F` in `<M>`, pick representatives
  `(h_i(g))_i` of each `g` in `F`. Since the elements of `F` are distinct and
  products agree modulo `N_omega`, for `omega`-many `i` the maps
  `g -> h_i(g)` have defect below any `eps` and separation above
  `min over g != 1 of lim_omega l_i(h_i(g)) / 2 > 0`. Separation constants can be
  rescaled to `1` as in the other route.
- **Contradiction.** The prerequisite makes `<M>` surjunctive.

This route and `weak-sofic-surjunctivity-from-metric-ultraproducts` form an
intended equivalence cycle.

**Verification.** `w3-vf-positive` passed this route (Section 3.4 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`). The per-set separation is rescaled to a uniform constant, as checked there.
