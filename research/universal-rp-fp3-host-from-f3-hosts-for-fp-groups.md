---
rg: 2
id: universal-rp-fp3-host-from-f3-hosts-for-fp-groups
kind: route
title: "F_3 hosts for all finitely presented groups give a recursively presented FP_3 host of a universal finitely presented group"
target: universal-fp-group-embeds-in-an-rp-fp3-group
requires:
  - every-finitely-presented-group-embeds-in-an-f3-group
---

A universal finitely presented group `U` is finitely presented. So the
required claim gives an embedding `U → K` with `K` of type `F_3`.

- A group of type `F_3` has a classifying space with finite 2-skeleton, so
  `K` is finitely presented and hence recursively presented.
- Cellular chains of the universal cover give a free resolution of `Z` over
  `ZK`, finitely generated in degrees `≤ 3`, so `K` is of type `FP_3`.

So `K` is a recursively presented host of type `FP_3` for `U`.

With `f3-hosts-for-fp-groups-via-universal-rp-fp3-host` this records an
equivalence. The two routes form a dependency cycle, and `cairn check` warns
about it. Both implications are true: the least fixpoint never fires a cycle,
so neither claim establishes itself. Do not delete either route to silence
the warning.
