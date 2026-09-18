---
rg: 2
id: rich-2to1-from-perfect-completeness
kind: route
title: Perfect-completeness rich 2-to-1 hardness gives near-perfect rich 2-to-1 hardness by the identity map
target: rich-2to1-games-conjecture
requires: [rich-2to1-perfect-completeness-conjecture]
---

Immediate. Every instance of value 1 has value `>= 1 - eps`. The NO condition
`val <= delta` is the same in both problems. So the identity map reduces
`Gap-Rich-2-to-1_n[1, delta]` to `Gap-Rich-2-to-1_n[1 - eps, delta]` for every
`eps >= 0`. NP-hardness of the first gives NP-hardness of the second with the
same `n(delta)`.

This route uses a strictly stronger premise than its target, and that is on
purpose. It puts BKM Conjecture 7 inside the cone of
`unique-games-conjecture`, so a kill of a perfect-completeness method is
visible from the target. It is not proposed as the easier way in:
`perfect-completeness-rich-2to1-tractable-skeletons-are-in-p` shows that every
known way to produce rich instances (right merges, certified affine-local
wrappers, affine encodings) is polynomial-time solvable at perfect
completeness.
