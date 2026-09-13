---
rg: 2
id: uncountably-many-fp2-groups-have-faithful-ha2-actions
kind: claim
title: "Uncountably many pairwise non-isomorphic groups of type FP_2 admit faithful actions of type [HA_2]"
distinct_from:
  every-countable-group-lies-in-a-faithful-ha2-actor: that asks for a faithful [HA_2] overgroup of every countable group (Problem 1.25 through twisted Brin–Thompson groups); this asks only for an uncountable family of faithful [HA_2] actor groups, which suffices for the first part of Problem 1.20
  uncountably-many-simple-groups-of-type-fp2: that asks for uncountably many simple FP_2 groups; this asks for uncountably many FP_2 groups with faithful [HA_2] actions, which yields that through twisted Brin–Thompson groups, while no argument is known that simple FP_2 groups carry faithful [HA_2] actions
---

There is a family of groups `G_i` of type FP_2 (over `Z`), realizing
uncountably many isomorphism types, each with a faithful action `G_i ↷ S_i` of
type `[HA_2]`: finitely many orbits on `S_i × S_i` and finitely generated point
stabilizers (Fournier-Facio–Wu–Zaremsky, arXiv:2603.24687v2, definition before
Corollary 4.14).

Route into the first part of Problem 1.20:
`uncountably-many-simple-fp2-via-faithful-ha2-actors`.

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2), **a fixed actor group gives countably
  many actions.** For one finitely generated `G`, an action with finitely many
  orbits and finitely generated point stabilizers is a finite disjoint union of
  coset actions `G/B_j` with `B_j` finitely generated. `G` has countably many
  finitely generated subgroups, so there are countably many such actions. The
  variety must therefore come from the groups `G_i`, or from quotients of one
  actor by uncountably many perfect normal subgroups with faithful orbit
  partitions (`perfect-orbit-quotients-of-fp2-actors-are-ha2-actors`).
- **Leary's groups (open).** `G_L(S)` (arXiv:1512.06609) realize `2^aleph_0`
  isomorphism types of FP_2 groups when `π_1(L)` is perfect. They act freely and
  cocompactly on level sets of CAT(0) cube complexes, but those actions have
  infinitely many pair orbits (unbounded distances). An FP_2 overgroup with a
  faithful `[HA_2]` action is needed. The 1.25 lane is checking lampshuffler
  groups `FSym(Γ) ⋊ Γ` for one-ended FP_2 `Γ` such as `G_L(S) × Z`; if they are of
  type FP_2 with finitely generated point stabilizers, this claim follows.
- **Restriction quotients (open).** `A(G)` for `G = G_V × (Z ⋉ {0,1}^Z)`, acting on
  a countable orbit inside `C × Y`, restricts to the simple groups
  `A(G|_{C×Y})` (`v-times-shift-alternating-group-restrictions-are-simple`).
  Faithfulness on the orbit holds because the orbit is dense in `C × Y`. The
  finiteness of pair orbits and of the stabilizers has not been checked, and
  type FP_2 of the quotients is the open core of
  `uncountably-many-simple-fp2-via-v-times-shift-restrictions`.
