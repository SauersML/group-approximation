---
rg: 2
id: ternary-rank-kill-via-anti-central-defect-deficit
kind: route
title: A strict defect drop under compression is impossible at an attained minimizer, so no anti-central rank function exists on the ternary Leavitt unit group algebra
target: sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one
requires:
  - ternary-anti-central-disjoint-defects-have-a-strict-deficit
  - ternary-anti-central-two-root-defect-has-a-uniform-gap
  - ternary-cylinder-defect-products-descend-in-sign-sectors
  - sylvester-rank-functions-compress-along-commuting-elements
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

Artifact Section 5.

1. **Minimizer.** If some anti-central Sylvester rank function exists, the gap claim gives one, `N_0`, with
   `N_0(D) = c_3 > 0`.
2. **Compression.**
   * Take disjoint nonempty proper cylinders `A` and `B` with proper union.
   * Item 1 of the deficit claim gives `N_0(D_A D_B) > 0`. So `h = N_0(Q_B D_A) > 0`, by the positivity item of
     the descent claim.
   * `N_0'(X) = N_0(F_3[iota_B](X) Q_B D_A)/h` is then anti-central.
3. **Contradiction.** The descent lower bound gives `N_0'(D) >= c_3 = N_0(D)`. The deficit gives
   `N_0'(D) <= theta N_0(D) < N_0(D)`.
4. **Conclusion.**
   * No anti-central function exists.
   * If some Sylvester rank function `N` had `N(1 - [z]) > 0`, then `N(eps_-) = N(1 - [z]) > 0`, and
     `X -> N(X eps_-)/N(eps_-)` would be anti-central.
   * So `N(1 - [z]) = 0` for every `N`. QED
