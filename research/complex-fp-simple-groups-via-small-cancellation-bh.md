---
rg: 2
id: complex-fp-simple-groups-via-small-cancellation-bh
kind: route
title: Put a classical C'(1/6) group of prescribed word-problem hardness into a finitely presented simple group and transfer the hardness upward
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires: [graphical-small-cancellation-inputs-satisfy-boone-higman, small-cancellation-groups-realize-every-wp-complexity]
---

Fix a recursive `T` and let `T^(m) = max_(k<=m) T(k)` be its monotone majorant.

1. By item 4 of `small-cancellation-groups-realize-every-wp-complexity`,
   applied to `T^`, there is a decidable `A` such that the two-generator classical `C'(1/6)` group `G_A`
   has solvable word problem but no algorithm in time `C*T^(C*l) + C*l + C`.
2. Classical `C'(1/6)` presentations are graphical `Gr'(1/6)` with cycle components. So
   by `graphical-small-cancellation-inputs-satisfy-boone-higman` (OPEN), `G_A ≤ S` for
   some finitely presented simple group `S`.
3. Suppose `S` had a word-problem algorithm in time `C*T(C*l) + C*l + C`, which is at
   most `C*T^(C*l) + C*l + C`. The length-linear substitution of item 5 of the
   complexity node, together with monotonicity of `T^`, would then give one for `G_A`
   in time `C'*T^(C'*l) + C'*l + C'`. That contradicts step 1. `∎`
