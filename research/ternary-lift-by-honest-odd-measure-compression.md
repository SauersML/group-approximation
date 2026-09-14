---
rg: 2
id: ternary-lift-by-honest-odd-measure-compression
kind: route
title: Lift the Dirac Hilbert hotel to the odd-measure crossed product by clopen pieces and Thompson translates
target: odd-measure-crossed-product-unit-below-cylinder-idempotent
requires: [signed-thompson-algebra-is-odd-measure-crossed-product]
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

**Dead.** Invalidated by `odd-measure-space-has-no-honest-thompson-compression`.

**The plan.** On the Dirac measures, the isometry `s0 = g_1 P_[0] + g_2 P_[1]`, with `g_1(0x) = 00x`
and `g_2(1x) = 01x`, is an honest compression of `X` into `[0]`. The plan was to realize it on all of
`M_-` as `v = sum [g_i] 1_(A_i)`: a clopen partition whose translates are pairwise disjoint inside
`{mu([0]) = 1}`.

**Why it dies.** Real Haar measure on `M_-` is `V`-invariant with `lambda(mu([0]) = 1) = 1/2`, so no
such pieces exist. The natural pieces fail concretely, because the images `{mu(00) = 1}` and
`{mu(01) = 1}` overlap on non-positive measures.
