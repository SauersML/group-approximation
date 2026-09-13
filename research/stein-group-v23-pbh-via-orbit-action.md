---
rg: 2
id: stein-group-v23-pbh-via-orbit-action
kind: route
title: V_{2,3} has a type (A) orbit action once it is finitely presented
target: stein-group-v23-subgroups-satisfy-pbh
requires:
  - pl-rearrangement-groups-have-two-transitive-orbit-actions
  - stein-groups-t23-and-v23-are-finitely-presented
---

**Proof.** `A = Z[1/6]` and `P = <2,3>` satisfy the hypotheses of
`pl-rearrangement-groups-have-two-transitive-orbit-actions`, whose proof checks them:
`2` and `3` are units, `m/6^k` is a sum of `m` copies of `6^{-k} ∈ P`, and
`1 = 1/2 + 1/2`. By `stein-groups-t23-and-v23-are-finitely-presented`, `V_{2,3}` is
finitely presented. So part 3 of that theorem makes the action on `Z[1/6] ∩ [0,1)` of
type (A), and every subgroup of `V_{2,3}` satisfies permutational Boone--Higman, has
solvable word problem, and embeds in a finitely presented simple group. `T_{2,3}` is the
subgroup of circle homeomorphisms, so it is covered. ∎
