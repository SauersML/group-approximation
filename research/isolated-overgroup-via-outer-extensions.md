---
rg: 2
id: isolated-overgroup-via-outer-extensions
kind: route
title: An outer extension of a finitely presented simple group containing the input is an isolated overgroup
target: every-decidable-group-embeds-in-an-isolated-group
requires:
  - decidable-groups-embed-in-outer-extensions-of-fp-simple-groups
  - outer-extensions-of-fp-simple-groups-are-isolated
---

Let `G` be finitely generated with solvable word problem.
- By `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`, there
  is an extension `1 → S → I → Q → 1` with `S` finitely presented, simple and
  nonabelian, `Q` finitely presented, `Q → Out(S)` injective, and `G ≤ I`.
- By `outer-extensions-of-fp-simple-groups-are-isolated`, `I` is isolated.

So `G` embeds in an isolated group.
