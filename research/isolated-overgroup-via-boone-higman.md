---
rg: 2
id: isolated-overgroup-via-boone-higman
kind: route
title: A finitely presented simple overgroup is an isolated overgroup
target: every-decidable-group-embeds-in-an-isolated-group
requires:
  - boone-higman-conjecture
  - fp-simple-groups-are-isolated
---

Let `G` be finitely generated with solvable word problem. By
`boone-higman-conjecture`, `G` embeds in a finitely presented simple group
`S`, and by `fp-simple-groups-are-isolated`, `S` is isolated. So `G` embeds in
an isolated group.

This is the implication CGP note after their Question 4, where they call the
Boone--Higman question "stronger".
