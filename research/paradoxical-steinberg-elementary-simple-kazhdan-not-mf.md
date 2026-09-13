---
rg: 2
id: paradoxical-steinberg-elementary-simple-kazhdan-not-mf
kind: claim
title: Over a finitely generated Steinberg algebra of a minimal effective Hausdorff ample groupoid containing a full one-sided inverse, EL_N mod centre is simple Kazhdan with no MF quotient
distinct_from:
  paradoxical-steinberg-families-kazhdan-no-mf-quotient: that gives finite generation, (T) and no MF quotient for two families without simplicity; this is the interface theorem adding simplicity modulo centre for every minimal effective Hausdorff ample groupoid.
  paradoxical-cantor-actions-give-simple-kazhdan-not-mf: that is the transformation-groupoid case, with the full defect built from an elementary paradox; this takes the full defect as a hypothesis and covers non-transformation groupoids (self-similar, products of Cuntz groupoids).
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed; proof in `paradoxical-steinberg-elementary-simple-kazhdan-not-mf-proof`).**

**Setting.** `𝒢` is a Hausdorff ample groupoid with compact infinite unit space, effective and minimal. `q` is a prime
power and `A = A_(F_q)(𝒢)`. Assume:
- `A` is finitely generated as a ring;
- `A` contains `s, t` with `ts = 1` and `A(1 - st)A = A`, e.g. a unital copy of `L_(F_q)(1, m)` with `m >= 2`.

**Statement.** For `N >= 3`, `EL_N(A)/Z(EL_N(A))` is an infinite finitely generated simple group with property (T).
Every homomorphism from it, or from `EL_n(A)` for `n >= 2`, to an MF group is trivial.

**Instances** (artifact part 2):
- Nekrashevych groupoids of pseudo-free self-similar actions, e.g. the odometer:
  `odometer-nekrashevych-elementary-simple-kazhdan-not-mf`.
- Products of Cuntz groupoids, `L(1,m) ⊗ L(1,n)`: `product-two-graph-kp-elementary-simple-kazhdan-not-mf`.
- Hausdorff minimal essentially principal Katsura triples with a properly infinite unit.

**Firewall.** `grigorchuk-steinberg-algebra-not-simple-over-f2`: the Grigorchuk groupoid is not Hausdorff and its
algebra over `F_2` is not simple, so this theorem does not apply there.

**Review (un-verify-3, 2026-09-13): PASS.** Interface theorem: the reviewed simplicity theorem plus `full-defect-ring-non-mf-at-rank-two`; the Leavitt copy gives `t_2(1 − s_1t_1)s_2 = 1`. `research/artifacts/un-review3-2026-09-13-part4.md` §3.
