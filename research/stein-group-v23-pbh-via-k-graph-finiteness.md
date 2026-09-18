---
rg: 2
id: stein-group-v23-pbh-via-k-graph-finiteness
kind: route
title: V_{2,3} is the full group of a one-vertex 2-graph, hence F_infinity, so its breakpoint action is of type (A) and all its subgroups satisfy permutational Boone--Higman
target: stein-group-v23-subgroups-satisfy-pbh
requires:
  - integral-slope-stein-v-groups-are-k-graph-full-groups
  - pl-rearrangement-groups-have-two-transitive-orbit-actions
---

**Proof.** This is `integral-slope-stein-v-groups-are-k-graph-full-groups` for `n = (2,3)`, which are
multiplicatively independent. That node gives:
- `V_{2,3}` is of type `F_∞`, so it is finitely presented;
- it acts with type (A) on `Z[1/6] ∩ [0,1)` (item 4).

Independently, the hypotheses of `pl-rearrangement-groups-have-two-transitive-orbit-actions` hold for
`A = Z[1/6]` and `P = ⟨2,3⟩`, as checked in `stein-group-v23-pbh-via-orbit-action`. Its part 3 turns
finite presentation into type (A) for the same action.

So every subgroup of `V_{2,3}` satisfies permutational Boone–Higman, has solvable word problem, and embeds
in a finitely presented simple group. This includes `T_{2,3}`, the subgroup of circle homeomorphisms,
and every finitely presented simple subgroup. `V_{2,3}` is itself simple (item 3 there, since
`gcd(1,2) = 1`).

This route does not need `stein-groups-t23-and-v23-are-finitely-presented`, whose `T_{2,3}` half stays
open. ∎
