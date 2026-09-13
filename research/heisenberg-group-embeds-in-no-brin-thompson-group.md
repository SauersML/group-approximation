---
rg: 2
id: heisenberg-group-embeds-in-no-brin-thompson-group
kind: claim
title: The integer Heisenberg group H_3(Z) embeds in no Brin-Thompson group mV
distinct_from:
  heisenberg-group-embeds-in-some-brin-thompson-group: that is the affirmative statement; this is its negation.
  thompson-v-has-no-heisenberg-subgroup: that is the case m = 1, established by undistortion; this claims every m, where undistortion fails.
---

For every `m >= 1`, `H_3(Z)` is not isomorphic to a subgroup of `mV`. The case
`m = 1` is `thompson-v-has-no-heisenberg-subgroup`. This claim gives Zaremsky
2.19(c) the answer no, through `some-gl-n-z-in-no-nv-via-heisenberg`.

## Attempts

- 2026-09-13 (lane z2-19-glnz-q-2v, unreviewed): the metric route is dead for
  `m >= 2`. Distortion elements exist (`brin-thompson-mv-contains-a-distortion-element`),
  so a proof must use the commutation relations, not only distortion of the
  central commutator. The next step is to test whether a drift-free element of
  `2V` can have a centralizer containing two non-commuting elements whose
  commutator it is.
