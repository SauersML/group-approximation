---
rg: 2
id: out-fm-aut-embedding-via-virtual-embedding
kind: route
title: Every Out(F_m) embeds in some Aut(F_n) once a finite-index subgroup does in each rank at least three
target: every-out-free-group-embeds-in-some-aut-free-group
requires:
  - out-free-groups-virtually-embed-in-aut-free-groups
  - aut-free-embeddability-passes-to-finite-index-overgroups
  - low-rank-out-free-groups-embed-in-aut-free-groups
---

- **m ≤ 2.** `low-rank-out-free-groups-embed-in-aut-free-groups`.
- **m ≥ 3.** By `out-free-groups-virtually-embed-in-aut-free-groups` some
  finite-index `L ≤ Out(F_m)` embeds in some `Aut(F_k)`. Item 2 of
  `aut-free-embeddability-passes-to-finite-index-overgroups` then embeds `Out(F_m)`
  in `Aut(F_{dk})` with `d = [Out(F_m) : L]`.

The converse implication is the route `out-fn-virtual-embedding-from-full-embedding`.
Together the two routes form a cycle through these two claims. That is intended:
they record an equivalence, both implications are correct, and neither route
should be deleted.
