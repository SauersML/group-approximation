---
rg: 2
id: fpbs-malnormal-coset-cycles-linear-perimeter-proof
kind: route
title: Suppress the union tree of a coset polygon to at most 4k-3 short arcs and bound edge multiplicity by ball truncations
target: fpbs-malnormal-coset-cycles-linear-perimeter
requires:
  - fpbs-malnormal-coset-cycles-bounded-syllables
artifacts:
  - research/artifacts/fpbs-malnormal-coset-cycles-linear-perimeter-2026-09-17.md
---

A complete proof is in the artifact. It imports only Item 1 of
[[fpbs-malnormal-coset-cycles-bounded-syllables]], verbatim: "For distinct
cosets `gH != g'H`, the convex hulls of `gH` and `g'H` in `T` meet in a
subtree of diameter less than `D`". It also imports the loop-erasure step of
that node's Item 3: "Every detour for `e(g)` contains a simple path from `gH`
to `gtH` that avoids `e(g)`. Adding `e(g)` gives a simple cycle with one more
`t`-edge. Edge-disjoint detours contain edge-disjoint simple paths, which give
distinct cycles."

1. **Short arcs.** Let `Σ` be the union of the `2k` polygon sides. Suppress
   the unmarked degree-2 vertices. This leaves at most `4k-3` arcs, and every
   side is a union of arcs. By crossing parity every arc lies on at least two
   sides. If two of them are coset sides, the arc has length `< D`. Otherwise
   one is a `t`-side, and the arc has length `<= τ`.
2. **Bounded multiplicity.** Take coset sides of distinct cosets through an
   edge `e`. They have distinct traces on the `D`-ball around `e`. Otherwise
   they share a segment of length `> D`, or they share an endpoint, and cosets
   are disjoint. Also, at most `2τ` `t`-sides contain `e`.
3. **Perimeter.** The perimeter is `sum_e mult(e) <= B |Σ|`.
4. **Consequences.** Counting words gives items 2 and 3. Syllable inclusion
   and the shift `Ad(t)` give item 4.
