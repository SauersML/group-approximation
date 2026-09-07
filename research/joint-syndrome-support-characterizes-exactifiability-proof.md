---
rg: 2
id: joint-syndrome-support-characterizes-exactifiability-proof
kind: route
title: Exclude impossible positive-probability labels and prepare a kernel vector for each remaining label
target: joint-syndrome-support-characterizes-exactifiability
requires: []
artifacts:
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
---

Theorem 1 of the artifact gives both directions. Nonzero positive `E_S`
occurs on some pure input, so exact output requires a nonzero common kernel
outside `S`. Conversely, select a unit vector in each nonzero common kernel;
discarding the post-measurement state and preparing that vector is CPTP and
exact. Zero-effect labels impose no condition on the chosen recovery there.

For the dilation statement, `W=sum_S |S> tensor sqrt(E_S)` is an isometry
because `sum_S E_S=I`; testing each label bit gives mutually commuting
one-qubit projections whose compressed joint effects are the original
`E_S`. This is the standard finite Naimark construction. Section 2 states
the missing implementation and locality bounds explicitly.
