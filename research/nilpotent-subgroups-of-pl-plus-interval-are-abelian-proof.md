---
rg: 2
id: nilpotent-subgroups-of-pl-plus-interval-are-abelian-proof
kind: route
title: Centralizers act abelianly on a bump, so a central commutator dies on its own bumps
target: nilpotent-subgroups-of-pl-plus-interval-are-abelian
requires: []
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part1.md
---

Full derivation in the artifact, Lemmas A and B, Corollary C and §N1. Summary:

- Commuting PL maps preserve each other's bumps.
- An element commuting with `f` and equal to the identity near the left endpoint `p`
  of a bump `B` of `f` is the identity on `B`. So the centralizer of `f`, restricted to
  `B`, embeds in `R` via `log g'(p+)` and is abelian.
- If `H` is nilpotent and not abelian, take `x` and `y` in `Z_2(H) \ Z(H)` with
  `z = [x,y] ≠ 1` central. On a bump `B` of `z`, the maps `x` and `y` preserve `B` and
  have commuting restrictions, so `z|_B = id`. That is a contradiction.
