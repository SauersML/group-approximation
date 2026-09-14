---
rg: 2
id: klein-fullness-gives-swap-fullness
kind: route
title: Fullness of the Klein averaging idempotent gives fullness of the swap averaging idempotent
target: projective-ternary-swap-idempotent-is-full
requires: [projective-ternary-klein-idempotent-is-full]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

`K` contains `wbar`, so `e_K = ebar e_K = e_K ebar`. From `c e_K b = 1` put
`c' = c e_K` and `b' = e_K b`. Then `c' ebar b' = c e_K b = 1`.

This is a strengthening, not a rename. `e_K` is a proper subidempotent of `ebar`,
and fullness of `ebar` does not imply fullness of `e_K` by any argument here.
