---
rg: 2
id: turing-machine-group-rtm-2-1-is-a-t-menable
kind: claim
title: "The group RTM(2,1) of reversible binary Turing machines (equivalently the Jacobian subgroup M_2 of 2V) has the Haagerup property"
distinct_from:
  full-shift-topological-full-group-is-a-t-menable: that asks Haagerup for [[X]], which is a subgroup of M_2 = RTM(2,1) and has no recorded distortion element; this asks it for all of M_2, which contains a distortion element, so no cubical or wall proof can reach it
  brin-thompson-groups-nv-are-a-t-menable: that is the goal for nV; this is a necessary prerequisite, sitting between the [[X]] prerequisite and 2V
  nv-jacobian-subgroup-contains-turing-machine-distortion: that proves M_2 = RTM(2,1) and that it contains a distortion element; this is the Haagerup question for that group
---

**Statement.** The group of reversible Turing machines `RTM(2,1)` (Callard–Salo, arXiv:2208.00685,
Definition 6.1, with 2 tape symbols and 1 head state) has the Haagerup property. Equivalently, by
item 1 of `nv-jacobian-subgroup-contains-turing-machine-distortion`, the Lebesgue-preserving
subgroup `M_2 = {g ∈ 2V : g_*λ = λ}` has the Haagerup property.

## Status

OPEN. It is a **necessary prerequisite** of `brin-thompson-groups-nv-are-a-t-menable`, through the
route `turing-machine-group-rtm-2-1-a-t-menable-from-nv`, and it can fail on its own.

## Known

- `[[X]] ≤ M_2` (item 3(c) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`). So this claim
  implies `full-shift-topological-full-group-is-a-t-menable`.
- `M_2` contains a finitely generated subgroup with an element `f` of infinite order and
  `|f^N| = O(log^4 N)` (`nv-jacobian-subgroup-contains-turing-machine-distortion`, item 2). So no
  commensurating action of `M_2` is proper. Any proof must be a genuinely non-cubical cnd function.
  Its values along `⟨f⟩` must tend to infinity while staying `O(log^8 N)`.
- `M_2` carries the unbounded measured-wall cnd function `ψ_M(g) = ∫|c(g)_1| dλ` (item 6(c) of the
  Jacobian node). It is subadditive on `M_2`, so `ψ_M(f^N) = O(log^4 N)`. It is not proper on
  `M_2`, because it vanishes on the infinite group `K ∩ M_2 = K`.
- The Callard–Salo element is expected to be a.e. locally periodic with geometrically distributed
  germ size (`callard-salo-element-is-ae-locally-periodic`, OPEN). If so, a proper cnd function
  must pick up its growth along `⟨f⟩` from exponentially rare long conveyor belts.

## Attempts

- **2026-09-19 (swarm-0917-w17-w17-nv-last1). Two obvious attacks, both dead; the third is
  deferred.**
  1. *Walls, cube complexes, commensurated sets.* Dead. The step is item 3 of
     `nv-jacobian-subgroup-contains-turing-machine-distortion`. Along the distorted element `f`,
     every commensurating length is `o(N)`, hence bounded by the bounded-or-linear dichotomy, so it
     cannot be proper.
  2. *The Maharam measured wall `ψ_M`.* Not proper. It vanishes on the infinite locally finite
     subgroup `K ≤ M_2`, since `c ≡ 0` there, and along `⟨f⟩` it is `O(log^4 N)`.
  3. *Deferred: `ψ_M` plus a cnd function proper on `K`.* The next step is to test `ψ_M + ψ_K`,
     with `ψ_K` a cnd function on `M_2` that is proper on `K`. The existence of `ψ_K` is the
     restriction to `M_2` of P3 (`brin-thompson-nv-cnd-proper-on-cocycle-kernel`). Even granting
     it, `ψ_M` does not supply the half "proper modulo `K`".
     - For the brick `B_m = [0^m]×[0^m]`, the local baker's map `b_m` is the prefix replacement
       `[0^m e]×[0^m] → [0^m]×[0^m e]` (`e ∈ {0,1}`), extended by the identity. It lies in `M_2`, has
       `c(b_m) = (−1, 1)` on `B_m` and `0` off it, and `ψ_M(b_m) = λ(B_m) = 4^{−m}`.
     - For `m < m'`, the cocycle of `b_m^{-1} b_{m'}` equals `(1, −1)` on the non-empty set `B_m \ B_{m'}`
       (there `b_{m'}` is the identity), so the `b_m` lie in
       pairwise distinct cosets of `K`.
     So `ψ_M` is bounded on infinitely many cosets of `K`. A proof of this route would still need a
     cnd function on `M_2` that is proper modulo `K`, and that is the `M_2` restriction of P1 ∧ P2 of
     `brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination`. So the attack reduces to the
     open halves of the goal and gives no independent route. It is recorded as deferred, not dead.
