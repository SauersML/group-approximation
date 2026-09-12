---
rg: 2
id: doubled-odd-amplification-erases-iwahori-parabolic-defect
kind: claim
title: Two odd-cycle amplifications erase the Iwahori parabolic sheet defect exactly
artifacts:
  - research/artifacts/dyadic-iwahori-random-lift-audit-2026-08-21.md
distinct_from:
  unamplified-iwahori-sheets-have-two-thirds-defect: that proves a 2/3 defect on raw three-sheet blocks; this proves the defect disappears exactly after a two-copy odd-cycle amplification.
  iwahori-question-as-square-root-of-parabolic: that requires the square root to extend together with an involution to the full second modular vertex; this solves only the parabolic permutation equation and explicitly does not claim that extension.
---

Let `tau` be a transposition of a three-point set, and let `s` be a
permutation all of whose cycles have odd length.  On two copies of the
product set, put

```text
P = 1_{two copies} x tau x s.
```

Then `P` is an exact square in the finite symmetric group.  In particular,
the support mismatch in
`unamplified-iwahori-sheets-have-two-thirds-defect` is not stable under
amplification.

For the dyadic problem one may take `s` to be the parabolic in a regular odd
congruence quotient of `PSL_2(Z)`: its cycles all have the same odd prime
length.  Thus the first modular vertex itself supplies arbitrarily large
exact finite actions whose amplified parabolic satisfies the required
square equation.

What remains is simultaneous: choose the square root as `x'y'` with
`x'^2=y'^3=1`, satisfy the second Iwahori involution relation, and retain
Bass--Serre normal-form separation.  No obstruction depending only on the
single parabolic permutation can rule out the random-lift route.

