---
rg: 2
id: stein-and-irrational-slope-f-groups-pbh-via-orbit-action
kind: route
title: Finite presentation of F_{2,3} and F_τ plus the interval orbit-action theorem
target: stein-and-irrational-slope-f-groups-satisfy-pbh
requires:
  - pl-interval-and-circle-groups-have-type-a-orbit-actions
  - stein-group-f23-is-of-type-f-infinity
  - irrational-slope-f-tau-is-of-type-f-infinity
---

**The models match.** For an increasing homeomorphism `f` of `[0,1]` with breakpoints in
`A` and slopes in `P ⊆ A`, the constants lie in `A` automatically. The first piece is
`f(x) = p_1 x`. Inductively, `f(x_i) ∈ A` and the next constant is
`f(x_i) − p_{i+1} x_i ∈ A`. So the imported groups `F_{2,3}` and `F_τ` are exactly
`F(Z[1/6], <2,3>)` and `F(Z[τ], <τ>)` in the notation of
`pl-interval-and-circle-groups-have-type-a-orbit-actions`.

**Hypotheses.** The proof of `pl-rearrangement-groups-have-two-transitive-orbit-actions`
checks (S), (R) and the unit condition for both pairs.

**Proof.** Both groups are finitely presented, by `stein-group-f23-is-of-type-f-infinity`
and `irrational-slope-f-tau-is-of-type-f-infinity`. Part 1 of
`pl-interval-and-circle-groups-have-type-a-orbit-actions` then gives type (A) actions on
`A ∩ (0,1)`, with stabilizers `F × F`. The subgroup consequences are part of that
theorem. ∎
