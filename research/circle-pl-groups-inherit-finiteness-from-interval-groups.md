---
rg: 2
id: circle-pl-groups-inherit-finiteness-from-interval-groups
kind: claim
title: Under Bieri–Strebel's conditions (S) and (R), the circle group T(A,P) is of type F_n whenever the interval group F(A,P) is; so T_{2,3} and T_τ are of type F_infinity, hence finitely presented, and their breakpoint actions are of type (A)
requires:
  - oligomorphic-actions-with-f-n-set-stabilizers-are-f-n
  - pl-rearrangement-groups-have-two-transitive-orbit-actions
  - pl-interval-and-circle-groups-have-type-a-orbit-actions
  - stein-group-f23-is-of-type-f-infinity
  - irrational-slope-f-tau-is-of-type-f-infinity
distinct_from:
  pl-interval-and-circle-groups-have-type-a-orbit-actions: that shows the circle action of T(A,P) is of type (A) exactly when T(A,P) is finitely presented; this proves the finite presentation from that of F(A,P).
  stein-groups-t23-and-v23-are-finitely-presented: that is the OPEN conjunction for T_{2,3} and V_{2,3}; this is its T half, and integral-slope-stein-v-groups-are-k-graph-full-groups is its V half.
  irrational-slope-t-tau-and-v-tau-are-finitely-presented: that is the OPEN conjunction for T_τ and V_τ, asserted by Burillo–Nucinkis–Reeves with proof deferred; this writes out the T half, and pisot-unit-slope-stein-groups-are-finitely-presented is the V half.
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). Burillo–Nucinkis–Reeves assert `F_∞` for
`T_τ` "by the methods of Stein" (arXiv:2006.02401, l.101), and Stein's 1992 paper presumably covers
`T_{2,3}`; neither proof was read. The argument below needs only `F(A,P)`.

## Statement

Let `A ⊆ R` be a subring and `P ≤ R_{>0}` a group of units of `A` satisfying (S) and (R), as in
`pl-rearrangement-groups-have-two-transitive-orbit-actions`. Let `T = T(A,P)` and `F = F(A,P)` be as in
`pl-interval-and-circle-groups-have-type-a-orbit-actions`.

1. If `F` is of type `F_n`, so is `T`. If `F` is `F_∞`, so is `T`.
2. `T_{2,3} = T(Z[1/6], ⟨2,3⟩)` and `T_τ = T(Z[τ], ⟨τ⟩)` are of type `F_∞`, in particular finitely
   presented. So are the index-two simple subgroup `T_{xz}` of `T_τ` (BNR, l.319) and every finite-index
   subgroup.
3. The 2-transitive actions of `T_{2,3}` and `T_τ` on `A ∩ [0,1)` are of type (A). So every subgroup of
   either satisfies permutational Boone–Higman.

## Proof

Let `O = A ∩ [0,1)`, the points of the circle `R/Z` with coordinates in `A`. By Lemma 1 (matching) of
`pl-rearrangement-two-transitive-orbit-action-proof`, any two intervals with endpoints in `A` and positive
lengths in `A` are matched by an increasing piecewise-linear bijection `h` with slopes in `P`, constants in
`A` and breakpoints in `A`.

1. **Transitive on cyclically ordered k-tuples.** Let `(x_1, …, x_k)` and `(x'_1, …, x'_k)` be in cyclic
   order in `O`.
   - The rotations `r_c` (`c ∈ O`) lie in `T`, as in the proof of
     `pl-interval-and-circle-groups-have-type-a-orbit-actions`, part 2. So we may take `x_1 = x'_1 = 0`.
   - Then `0 < x_2 < … < x_k < 1`, and likewise for the primed points. Lemma 1 on `[x_i, x_{i+1}]` and on
     `[x_k, 1]` glues to `f ∈ F ≤ T` with `f(x_i) = x'_i`.
   - A finite subset of the circle has a unique cyclic order, so `T` has **one orbit on k-element
     subsets** for every `k`. This is condition (O).
2. **Stabilizers.** Let `σ = {0 = x_1 < … < x_k}`, which we may assume after a rotation.
   - An element fixing `σ` pointwise fixes `0`, so it lies in `Stab(0) = F` (loc. cit., part 2). It
     restricts to the arcs, so the pointwise stabilizer is `F[x_1,x_2] × … × F[x_k,1]`.
   - Each factor is conjugate to `F` by a Lemma 1 matching `h: [0,1] → [x_i, x_{i+1}]`, since conjugation
     by `h` preserves slopes in `P` and breakpoints in `A`.
   - `T` preserves the cyclic order, so the setwise stabilizer `T_σ` maps to `Z/k` with kernel `F^k`.
   - A finite extension of `F^k` is `F_n` when `F` is. This is condition (St).
3. **Finiteness (item 1).** `oligomorphic-actions-with-f-n-set-stabilizers-are-f-n`.
4. **Item 2.**
   - (S) and (R) hold for both pairs, by the proof of `pl-rearrangement-groups-have-two-transitive-orbit-actions`
     (its last paragraph checks `Z[1/6], ⟨2,3⟩` and `Z[τ], ⟨τ⟩`).
   - `F_{2,3}` and `F_τ` are `F_∞` by `stein-group-f23-is-of-type-f-infinity` and
     `irrational-slope-f-tau-is-of-type-f-infinity`.
   - The models match, as in `stein-and-irrational-slope-f-groups-pbh-via-orbit-action`.
   - BNR's `T_τ`, the orientation-preserving piecewise-linear circle homeomorphisms with breakpoints in
     `Z[τ]` and slopes in `τ^Z`, is `T(Z[τ], ⟨τ⟩)`.
5. **Item 3.** `F` is finitely generated, so `pl-interval-and-circle-groups-have-type-a-orbit-actions`,
   part 2, makes the action of type (A) now that `T` is finitely presented. ∎

## Consequences

- `stein-groups-t23-and-v23-are-finitely-presented` is ESTABLISHED through
  `stein-groups-t23-and-v23-fp-via-simplex-and-k-graph`.
- `irrational-slope-t-tau-and-v-tau-are-finitely-presented` is ESTABLISHED through
  `irrational-slope-t-tau-and-v-tau-fp-via-simplex-and-pisot-coding`. That completes the route
  `irrational-slope-v-tau-pbh-via-orbit-action` of `irrational-slope-v-tau-subgroups-satisfy-pbh`.
- **BFFHZ Question 3.4.** `T_{xz}` and `V_{xz}` are finitely presented simple groups that lie in `B_A`.
  `T_{xz}` acts on the circle, the family BFFHZ single out as not MIF.

## Lesson for general BH

The circle adds nothing to finiteness. `T` is transitive on cyclic configurations, and each configuration's
stabilizer is a product of copies of the interval group, so the full simplex on one orbit transfers `F_n`
from `F` to `T`. The general principle is `oligomorphic-actions-with-f-n-set-stabilizers-are-f-n`. A host
whose finite-set stabilizers decompose into copies of one finitely presented piece is finitely presented,
and its orbit action is of type (A). So a constructive BH route never needs a separate finite-presentation
proof once it controls stabilizers of three points.
