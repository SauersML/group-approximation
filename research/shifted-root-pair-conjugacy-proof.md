---
rg: 2
id: shifted-root-pair-conjugacy-proof
kind: route
title: Check the explicit intertwiner entrywise, and separate the unit pair by the common-kernel invariant
target: shifted-root-pair-conjugates-to-idempotent-root-pair
requires: []
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Complete proof: artifact Section 6.1.

- **The intertwiner.** `g (e_0 E_12)` has column `2` equal to `g`'s column `1` times `e_0`, which
  is `(t_0, 0, 0)` since `t_1 e_0 = 0`. `(t_0 E_12) g` has row `1` equal to `t_0` times row `2`
  of `g`, which is `(0, t_0, 0)`. Both equal `t_0 E_12`. Likewise `g (e_0 E_23)` and
  `(s_0 E_23) g` both equal `e_0 E_23`.
- **Invertibility.** `g` is an isomorphism of right `R`-modules. It sends the chain
  `e_3 e_0 R -> e_2 e_0 R -> e_1 e_0 R` onto `e_3 R -> e_2 s_0 R -> e_1 R`, by `t_0`, the identity
  and `t_0`. It sends `(e_1 R)^3` onto `e_2 s_1 R`, through the decomposition
  `1 = s_0 t_0 + s_1 s_0 t_0 t_1 + s_1 s_1 t_1 t_1`.
- **Non-conjugacy.** The common kernel modulo the image sum is `e_1 R / e_1 R = 0` for the unit
  pair, and `(e_1 R (+) e_2 s_1 R) / e_1 R ~= s_1 R != 0` for the shifted pair.
