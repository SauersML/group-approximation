---
rg: 2
id: fpbs-pu-nonuniqueness-cannot-separate-proof
kind: route
title: Critical emptiness forces zero infinite clusters at a collapsed threshold
target: fpbs-pu-nonuniqueness-cannot-separate
requires:
  - fpbs-critical-no-infinite-cluster
---

**Part 1.** If `p_c = p_u`, then `fpbs-critical-no-infinite-cluster` gives
`N_infinity(p_u) = N_infinity(p_c) = 0`. In particular `N_infinity(p_u) != 1`.

**Part 2.** For the forward direction: if `p_u > p_c`, then `p_u` is
supercritical, so an infinite cluster exists almost surely. Quasi-transitivity
then gives `theta(p_u) > 0` at some vertex of each orbit.

For the reverse direction: if `theta(p_u) > 0`, an infinite cluster exists with
positive probability. Existence of an infinite cluster is a tail event, so it
has probability one, and `N_infinity(p_u) != 0`. Since `N_infinity(p_c) = 0`,
`p_u != p_c`, and `p_c <= p_u` always holds, so `p_c < p_u`.

Neither direction uses whether the infinite cluster at `p_u` is unique. That is
the precise sense in which a no-unique-infinite-cluster theorem at `p_u` adds
nothing to separation.
