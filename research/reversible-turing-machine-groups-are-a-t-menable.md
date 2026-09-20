---
rg: 2
id: reversible-turing-machine-groups-are-a-t-menable
kind: claim
title: "The group RTM(2,1) of reversible binary Turing machines, which is the Lebesgue-preserving subgroup M_2 of 2V, has the Haagerup property"
distinct_from:
  full-shift-topological-full-group-is-a-t-menable: that asks for a proper cnd function on the full-shift group [[X]], which has no distorted element; this asks for one on the overgroup RTM(2,1) = M_2, which contains the Callard--Salo distortion element, so it is strictly stronger and admits no cubical proof
  brin-thompson-groups-nv-are-a-t-menable: that is the goal for nV; this is its restriction to the Jacobian kernel M_2 of 2V, a necessary prerequisite that can fail on its own
  lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group: that identifies M_2 with RTM(2,1) and records the cubical kill; this is the open analytic question on that group
---

**OPEN.** `RTM(2, 1)` is the Barbieri–Kari–Salo group of reversible Turing machines with one state
on the binary tape. In the moving-tape model it is the group of homeomorphisms of `X = {0,1}^Z`
that, by a local rule of radius `r`, overwrite the window `[−r, r)` by a word of length `2r` cut
at a new origin. By `lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group`, item 1,
its conjugate by the baker's-map coding `Φ` is exactly the Lebesgue-preserving subgroup `M_2` of
`2V`. The claim is that it has a proper conditionally negative definite function.

## Role

- **Necessary for the goal.** Route `turing-machine-group-a-t-menable-from-nv`: `M_2 ≤ 2V`, so
  `brin-thompson-groups-nv-are-a-t-menable` for `n = 2` restricts to it.
- **Sufficient for the full-shift prerequisite.** Route
  `full-shift-full-group-a-t-menable-from-turing-machines`: `[[X]] ≤ M_2`.
- So the chain of necessary prerequisites is now
  `goal ⟹ RTM(2, 1) Haagerup ⟹ [[X]] Haagerup`. Each step can fail on its own.
  - The first step discards the Jacobian directions (Q_J).
  - The second discards the tape-overwriting (homoclinic) moves.

## Known

- **No cubical proof.** `RTM(2, 1)` contains `f` with `|f^N| = O(log^4 N)` (Callard–Salo,
  Theorem D). So it has no proper commensurating action
  (`lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group`, item 3(a)).
- **Not reached by the gap-class kill.** `M_2` contains no brick-local coordinate copy of `V`.
  The Maharam wall `ψ_M(g) = ∫ |c(g)_1| dλ` is an unbounded cnd function on it (item 6(c) of
  `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`). `ψ_M` is not proper: it vanishes on the
  whole kernel `K` of `c`, which is infinite.
- **Average movement.** `α(g) = ∫ c(g)_1 dλ` is a homomorphism `M_2 → Z[1/2]`. This is the
  Barbieri–Kari–Salo average movement of a machine, and it is additive because reversible machines
  preserve the measure. Its image contains `α(baker's map) = ±1`, so its kernel has infinite index. The kernel
  contains `K`. It also contains the Callard–Salo element `f`: `N|α(f)| = |α(f^N)| ≤ C|f^N|_F =
  O(log^4 N)` forces `α(f) = 0`. (Not used in any proof; recorded for orientation.)

## Attempts

None yet.
