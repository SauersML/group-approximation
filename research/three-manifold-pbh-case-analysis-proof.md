---
rg: 2
id: three-manifold-pbh-case-analysis-proof
kind: route
title: Reduce to orientable prime summands, then split by boundary, Seifert type, non-positive curvature and virtual fibering
target: three-manifold-groups-pbh-off-nonfibered-graph-manifolds
requires:
  - three-manifold-groups-linear-unless-closed-graph-manifold
  - virtually-fibered-3-manifold-groups-satisfy-pbh
  - char-zero-linear-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - aut-free-groups-satisfy-permutational-boone-higman
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

`B_A` is the class of `boone-higman-type-a-class-closed-under-finite-extensions`.
It is closed under subgroups, finite direct products and finite-index overgroups
(parts 1 and 2 there), and every group in it embeds in a finitely presented
simple group (part 3). BFFHZ Corollary F, recorded in
`aut-free-groups-satisfy-permutational-boone-higman`, closes it under free
products (arXiv:2503.21882v2, l.180--181: "If A and B satisfy the permutational
Boone–Higman conjecture, then the free product A ∗ B also satisfies the
(permutational) Boone–Higman conjecture"). Characteristic-zero linear groups are
in `B_A` by `char-zero-linear-groups-satisfy-permutational-boone-higman`. Item
numbers below refer to `three-manifold-groups-linear-unless-closed-graph-manifold`.

"AFW" is arXiv:1205.0202; line numbers are in its TeX source.

1. **Orientation.** `pi_1(N^+)` has index at most 2 in `pi_1(N)`. By part 2 it is
   enough to treat `N^+`.
2. **Sphere boundary.** Gluing a 3-ball to a 2-sphere boundary component does
   not change `pi_1`, by van Kampen, since both are simply connected.
3. **Prime decomposition.** AFW Theorem `thm:prime` (l.322--331): "In
   particular, π1(N) = π1(N1) ∗ ··· ∗ π1(Nr) is the free product of fundamental
   groups of prime 3-manifolds." By Corollary F it is enough to treat each
   `N_i`. AFW l.318: "if N is an orientable prime 3-manifold with no spherical
   boundary components, then by [Hem76, Lemma 3.13] either N is irreducible or
   N = S1 × S2". `pi_1(S^1 x S^2) = Z` is linear.
4. **Finite fundamental group.** A finite group embeds in `GL_n(Q)`.
5. **Infinite fundamental group.** AFW (C.1), l.1715--1718: an irreducible
   orientable `N_i` with infinite `pi_1` is an Eilenberg--MacLane space, i.e.
   aspherical.
   - **Non-empty boundary:** linear over `Z` (item 1).
   - **Closed, not a graph manifold:** linear over `Z` (item 3).
   - **Closed Seifert fibered:** linear over `Z` (item 2).
   - **Closed graph manifold, not Seifert fibered.** Its JSJ decomposition is
     non-trivial: with trivial JSJ decomposition the only JSJ component is
     `N_i`, which would then be Seifert fibered.
     - If `N_i` is non-positively curved, `pi_1(N_i)` is linear over `Z`
       (item 4).
     - If `N_i` is virtually fibered, `pi_1(N_i)` is in `B_A` by
       `virtually-fibered-3-manifold-groups-satisfy-pbh`.
     - Otherwise `N_i` is in the excluded class.

Every case lands in `B_A`, so `pi_1(N)` is in `B_A` by Corollary F and part 2.
The envelope is part 3; the twisted Brin--Thompson form is BFFHZ Theorem C.

**Trust surface.** The route rests on:
- the textbook topology in steps 2--5: van Kampen, prime decomposition,
  Hempel's lemma and asphericity, quoted from AFW and not rechecked at primary
  sources;
- the literature imports of the linearity node and of BFFHZ;
- the elementary case split in `virtually-fibered-3-manifold-pbh-proof`.
