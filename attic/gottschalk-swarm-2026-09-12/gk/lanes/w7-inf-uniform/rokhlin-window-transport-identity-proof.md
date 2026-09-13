---
rg: 2
id: rokhlin-window-transport-identity-proof
kind: route
title: Chain rule along an i.i.d. order plus left translation gives the Rokhlin window transport identity
target: rokhlin-window-random-order-transport-identity
requires: []
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
Artifact Section 2, Theorem 1.

1. `U` is independent of `x`, so `I(x(1); y_F) = I(x(1); y_F | U)`.
2. For fixed labels, the chain rule over `F` in increasing order gives `sum_f I(x(1); y_f | y_(F ∩ past(f)), U)`.
3. The shift `T_(f^-1)` preserves the law of `(x, U)`. It sends `x(1)` to `x(f^-1)`, `y_f` to `y_1`, and the past codewords `F ∩ past(f)` to `f^-1 F ∩ past(1)`.
4. Integrate over `U`.

The check on `Z` with the copy code (artifact Section 2) gives `1/2 + 1/2 = 1` bit.
