---
rg: 2
id: isolated-overgroup-via-locally-moving-hosts
kind: route
title: A finitely presented overgroup acting with a locally moving simple subgroup is an isolated overgroup
target: every-decidable-group-embeds-in-an-isolated-group
requires:
  - decidable-groups-embed-in-fp-locally-moving-groups
  - fp-groups-with-a-locally-moving-simple-subgroup-are-isolated
---

Let `G` be finitely generated with solvable word problem.
- By `decidable-groups-embed-in-fp-locally-moving-groups`, there is a finitely presented
  `Γ ≥ G` with a faithful action on `X` and `T ≤ Γ` satisfying (top) or (fin).
- By `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`, item 5, `Γ` is
  isolated.

So `G` embeds in an isolated group.

**Where it can fail.** Only in the first step: the second is established. The first
step sits between the permutational class and Question 4 in the chain of implications from the permutational class to Question 4
(see the Position section of the first requirement). A counterexample to it must be a
decidable group all of whose finitely presented overgroups lack every faithful locally
moving action. Such a group need not be a counterexample to Question 4.
