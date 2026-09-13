---
rg: 2
id: left-orderable-non-sofic-via-thompson-f
kind: route
title: If Thompson's F is not sofic, it is a left-orderable nonsofic group
target: left-orderable-non-sofic-group
requires: [thompson-f-is-not-sofic, thompson-f-is-bi-orderable]
---

`F` is bi-orderable (`thompson-f-is-bi-orderable`), hence left-orderable.  If
`F` is not sofic (`thompson-f-is-not-sofic`), then `F` itself is a
left-orderable nonsofic group.  ∎

**Why this route is not behind Navas's Question 3.**  Every other live route
into the root needs an infinite left-orderable Kazhdan group
(`infinite-left-orderable-kazhdan-group`).  This one cannot use one:

- `F` is bi-orderable, hence locally indicable, so it contains no nontrivial
  Kazhdan subgroup (the argument recorded in
  `left-orderable-group-with-rigid-compression-pair`, Attempts).
- `F` has the Haagerup property, so no rigid compression mechanism reaches it
  (`a-t-menable-groups-have-no-rigid-compression-defect`).

Its input is a different, finitary problem.  By
`thompson-f-sofic-iff-relator-system-unstable` (ESTABLISHED, not independently
reviewed), `thompson-f-is-not-sofic` is equivalent to Arzhantseva--Paunescu's
question whether the two relators of `F` are stable in permutations, that is,
whether almost-solutions in `Sym(n)` almost commute uniformly in `n`.

**Model test.**  The route fires only if `F` is not sofic.  The graph also
records the opposite claim `thompson-f-is-sofic`, which would close this route.
Both are open.
