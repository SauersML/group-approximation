---
rg: 2
id: boone-higman-via-decidable-edge-towers
kind: route
title: Upgrade a decidable HNN tower to a finitely presented simple envelope one step at a time
target: boone-higman-conjecture
requires: [decidable-groups-embed-in-decidable-edge-towers, bh-embeddability-survives-decidable-edge-hnn]
---

Let `G` be finitely generated with solvable word problem. By
`decidable-groups-embed-in-decidable-edge-towers`, choose
`B = K_0 <= ... <= K_n` containing `G`, with `B` embedding in a finitely
presented simple group. Every `K_j` is finitely generated.

By induction on `j`, `bh-embeddability-survives-decidable-edge-hnn` makes each
`K_j` embed in a finitely presented simple group. Its hypotheses are what the
tower supplies: finitely generated associated subgroups with decidable
membership in `K_j`, and a computable edge isomorphism. Hence `K_n`, and its
subgroup `G`, embed in a finitely presented simple group. `∎`

## What the two premises cost

- `bh-embeddability-forces-decidable-edge-membership` shows that the
  decidability hypothesis of the permanence premise is necessary, so the route
  gives nothing away there.
- `fa-subgroups-of-graph-towers-lie-in-base-pieces` shows that the tower premise
  contains Boone--Higman for decidable FA inputs. So this route reduces the
  conjecture only along non-FA structure; for Kazhdan inputs all of the
  difficulty sits in the base.
