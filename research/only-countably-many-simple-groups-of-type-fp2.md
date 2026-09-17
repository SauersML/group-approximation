---
rg: 2
id: only-countably-many-simple-groups-of-type-fp2
kind: claim
title: "Simple groups of type FP_2 realize at most countably many isomorphism types"
distinct_from:
  uncountably-many-simple-groups-of-type-fp2: that claim is the opposite answer to the same part of Problem 1.20; this is the countable bound
---

Up to isomorphism, there are at most countably many simple groups of type
FP_2 (over `Z`).

This is the negative answer to the first part of Zaremsky's Problem 1.20. It
implies the negative answer to the second part
(`only-countably-many-simple-groups-of-type-fp`).

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2): no obstruction known. By
  `simple-fp2-uncountability-via-perfect-simple-quotients`, this claim says
  that every finitely presented group has only countably many perfect normal
  subgroups with simple quotient. A proof would have to control non-recursive
  complexity: groups of type FP_2 need not be recursively presentable (Leary,
  arXiv:1512.06609, Theorem 1.2(4)), so Kuznetsov's argument that simple
  recursively presented groups have solvable word problem does not apply.
- 2026-09-17 (swarm-0917-w5-z-fp2-countable, census-computation): **the
  quotient-of-a-fixed-actor class of the opposite route is dead.** See
  `fixed-actor-orbit-quotients-are-finitely-many` (established).
  - **Invariant.** The lattice of unions of the `m` pair orbits of `P ↷ X`.
    It bounds the invariant equivalence relations by `2^(m-k)`. A perfect normal
    subgroup with faithful orbit partition is the kernel of one of those
    relations.
  - **Where it dies.** Every perfect orbit quotient of one actor, iterated or
    not, is one of at most `2^(m-k)` actors.
  - **What survives.** Kernels of type [A_2] actions give a countable class.
    In any uncountable family of faithful [HA_2] actors, all but countably many
    members have, for every finitely presented cover `H → G`, a point stabilizer
    in `H` that is not finitely generated.
  - This closes the second alternative left open on
    `uncountably-many-fp2-groups-have-faithful-ha2-actions` (2026-09-13).
  - The FFWZ route to uncountability must vary the actor group. For almost all
    members, the action must not be an orbit quotient of any type [A_2] action.
- 2026-09-17 (same lane), **observation, not a node: perfect-set dichotomy.**
  - **Setting.** For finitely generated `H`, let `M_H` be the set of perfect
    normal `N` with `H/N` simple, inside the compact Chabauty space `N(H)`.
  - **`M_H` is `G_δ`.** Properness is clopen. "`g ∈ N` or
    `s ∈ <<N, g>>`" is open for each `g` and each generator `s`, since
    membership in a normal closure is witnessed by finitely many elements of
    `N`. "`n ∉ N` or `n ∈ [N, N]`" is open for each `n`.
  - **Dichotomy.** `M_H` is Polish, so it is countable or contains a Cantor set.
    So this claim is equivalent to: no finitely presented `H` has a
    Cantor-embedded family of perfect maximal kernels. Every point of such a
    family is a Chabauty limit of the others, hence not finitely normally
    generated (`fng-maximal-kernels-are-isolated-proper-normal-points`).
  - **Status.** OPEN.
  - **Prerequisites that can fail independently.**
    - (P1) Every simple group of type FP_2 is finitely presented. This implies
      the claim. It is refuted by one faithful [HA_2] actor that is not finitely
      presented (FFWZ Corollary 4.2).
    - (P2) Every faithful [HA_2] actor is an orbit quotient of a type [A_2]
      action. This bounds the FFWZ route by the countable class `𝒞`, but does
      not imply the claim.
