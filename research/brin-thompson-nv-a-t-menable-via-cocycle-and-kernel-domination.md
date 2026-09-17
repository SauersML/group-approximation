---
rg: 2
id: brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination
kind: route
title: "Split the Haagerup property of nV into three independent dominations: scale of the exponent cocycle, depth of its pattern, and depth in the locally finite kernel"
target: brin-thompson-groups-nv-are-a-t-menable
requires:
  - brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination
  - brin-thompson-nv-exponent-cocycle-scale-is-cnd-dominated
  - brin-thompson-nv-exponent-cocycle-pattern-depth-is-cnd-dominated
  - brin-thompson-nv-cnd-proper-on-cocycle-kernel
---

**Not the triangular split.** `brin-thompson-nv-a-t-menable-via-triangular-split` splits along
`T_n`, whose fibre half contains infinite-order undistorted elements and Problem B for `Γ = V`.
This route splits along the torsion kernel `K` of the exponent cocycle, so the fibre half P3 is
about finite symmetric groups only. The transversal half is cut further into a magnitude statement
P1 and a positional statement P2 about the cocycle.

**Route.** Fix `n ≥ 2`. By `brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`, `nV` has
the Haagerup property iff all three prerequisites hold.

- **P1 (scale).** `brin-thompson-nv-exponent-cocycle-scale-is-cnd-dominated`: a cnd function
  `ψ_1 ≥ F(‖c(g)‖)`.
- **P2 (pattern).** `brin-thompson-nv-exponent-cocycle-pattern-depth-is-cnd-dominated`: a cnd
  function `ψ_2 ≥ F(pd(g))`.
- **P3 (kernel).** `brin-thompson-nv-cnd-proper-on-cocycle-kernel`: a cnd function on `nV` proper on
  `K = ker c = ⋃_m Sym(2^{nm})`.

Each prerequisite is necessary, so this route loses nothing, and a counterexample to any one of
them refutes the target for that `n` (for `n = 2` it proves `brin-thompson-2v-is-not-a-t-menable`).

**What each prerequisite is known to need.**

| | sees | known consequence | cubical? |
|---|---|---|---|
| P1 | values of `c`, magnitude only | implies Problem B for `Z` (supplement (c)) | no, dies on `id × x_0` |
| P2 | values of `c`, pattern only | `nV` analogue of the free positional half of Problem B | no, dies on `id × x_0` |
| P3 | finite pieces `K_m` | none recorded | not ruled out |

**Where the Callard–Salo element goes.** `f` has infinite order and `K` is torsion, so the powers
`f^N` (`N ∈ Z`) lie in pairwise distinct cosets of `K`. By supplement (a) at least one of
`‖c(f^N)‖`, `pd(f^N)` is unbounded over `N ∈ Z`,
and both are `O(log^4 N)`. Indeed `‖c‖` is subadditive, and `pd ≤ pd'`, where `pd'(h)` is the least
`m` such that `h` is a prefix replacement on every level-`m` cube, with
`pd'(gh) ≤ max(pd'(h), pd'(g) + ‖c(h)‖)`. So both are at most linear in word length. The dead measured-wall
lane `e-nv-walls` found `f` a.e. locally periodic with uniformly bounded germ size. That does not
decide between the two, since both are suprema and can grow on sets of small measure. The
computation is not done: it is the first test of this route.

**Attack order.**
1. *P2 on `⟨f⟩`* (computation): decide which of `‖c(f^N)‖` and `pd(f^N)` grows, from the
   Callard–Salo conveyor construction.
2. *P3* (finite models): a cnd function on `nV` whose restriction to each `Sym(2^{nm})` grows with
   the kernel depth. Test family: transpositions of two sibling level-`m` cubes. For `m ≥ 2`
   all are conjugate to `τ_2`, and every such conjugator has scale `≥ m − 2`, so P1 is compatible
   with P3 on this family.
3. *P1* (at least as hard as `cantor-integer-maps-sup-norm-is-cnd-dominated`).
