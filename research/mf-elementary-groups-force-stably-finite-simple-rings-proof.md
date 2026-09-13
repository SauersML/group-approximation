---
rg: 2
id: mf-elementary-groups-force-stably-finite-simple-rings-proof
kind: route
title: An infinite matrix amplification of a simple ring carries a full complementary idempotent
target: mf-elementary-groups-force-stably-finite-simple-rings
requires: [full-defect-in-m-by-m-kills-mf-quotients-of-el-2m]
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

1. **The defect.** `M_m(R)` is simple, since its two-sided ideals are the `M_m(I)`. Suppose it is not directly
   finite: take `x, y` with `xy = 1 ≠ yx` and set `t = x`, `s = y`.
   - Then `ts = 1 ≠ st`, and `e = 1 − st` satisfies `e^2 = 1 − 2st + s(ts)t = e`, so it is a nonzero idempotent.
   - The two-sided ideal of `e` is nonzero, hence equal to `M_m(R)`.

   `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m` then gives item 1 for every `N >= 2m`.
2. **Contrapositive.** Item 2 is item 1 read backwards. When `EL_N(R)` is MF and `R ≠ 0`, the identity map is a
   nontrivial homomorphism to an MF group, because `e_12(1) ≠ 1`.
3. **Stable version.** If item 2 holds for infinitely many `N`, then every `M_m(R)` is directly finite, which is
   stable finiteness. MF passes to subgroups, and `EL_N(R) ≤ EL_(N+1)(R)`, so "MF for infinitely many `N`" is the
   same as "MF for all `N`".
