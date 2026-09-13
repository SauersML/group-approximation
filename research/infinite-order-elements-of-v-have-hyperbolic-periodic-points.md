---
rg: 2
id: infinite-order-elements-of-v-have-hyperbolic-periodic-points
kind: claim
title: Every infinite-order element of Thompson's group V has a periodic point with nontrivial slope
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md
---

Let `g` be an element of Thompson's group `V` of infinite order, acting on
`{0,1}^ω` by finitely many prefix replacements. Then there are `k ≥ 1` and a point `p` with
`g^k(p) = p` and `(g^k)'(p) ≠ 1`. Here the slope is `2^{|u| − |v|}` for the local prefix
replacement `u w ↦ v w` of `g^k` around `p`.

This is an input from the structure theory of elements of `V`: revealing pairs, periodic
parts, and attractor–repeller flow components.

## Attempts

- 2026-09-13 (z2-15b-biorderable). Expected to be a direct consequence of revealing pairs
  (Brin, Geom. Dedicata 108 (2004); Salazar-Díaz, conjugacy in `V`). The statements were
  not read: arXiv was rate-limited and the search budget was exhausted, so there is no
  citation route yet.
- Direct proof attempt. Follow a long cone `D` under `g`. While the cone word stays longer
  than the pieces, each step replaces a bounded prefix. If lengths stay bounded, the orbit
  of cones repeats and some `g^n` is the identity on `D`. If some `g^n` maps `D` into
  itself by a single `w ↦ w r` with `r` nonempty, `w r^∞` is a hyperbolic fixed point.
  The missing step is the case where lengths grow without such a nesting, and the global
  conclusion that "identity on every cone of some partition" gives finite order.
