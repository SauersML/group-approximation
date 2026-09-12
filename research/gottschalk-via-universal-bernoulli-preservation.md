---
rg: 2
id: gottschalk-via-universal-bernoulli-preservation
kind: route
title: If injective automata preserve the uniform measure, full support makes them onto
target: gottschalk-surjunctivity-conjecture
requires:
  - every-injective-ca-preserves-uniform-bernoulli-measure
  - injective-measure-preserving-ca-is-surjective
artifacts:
  - research/artifacts/gottschalk-tree-calibration-and-bernoulli-preservation-2026-09-12.md
---

Apply the second prerequisite to each injective automaton, using the first. This
route and `bernoulli-preservation-from-gottschalk` record an equivalence, so the
open prerequisite is the goal restated automaton by automaton. The dependency
cycle is intended. The quantitative, per-site content is in
`gottschalk-via-maximal-bernoulli-rokhlin-entropy`.
