---
rg: 2
id: signed-swap-normally-generates-elementary-group
kind: claim
title: The signed basis swap normally generates every rank-at-least-three elementary group in every characteristic
distinct_from:
  char-two-basis-swap-normally-generates-elementary-group: that is the characteristic-two calculation, where the swap is the unsigned permutation matrix of order two and the cancellation uses e_13(r)^2 = 1; this uses the signed swap, which has order four, and the cancellation is e_13(2r)e_13(-r) = e_13(r), so no characteristic hypothesis remains.
  properly-infinite-unit-rank-two-normal-generator: that is a rank-two statement over a ring with a properly infinite unit, whose generator is a diagonal commutator; this is a rank-at-least-three statement over an arbitrary unital ring, whose generator is a torsion element.
  elementary-rank-descent-to-two: that moves a higher rank inside rank two; this stays in one rank and identifies a single torsion normal generator there.
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

Let `R` be a unital ring and `m >= 3`.  In `EL_m(R)` put

```text
a = e_12(1) e_21(-1) e_12(1) = [[0,1],[-1,0]] (+) I_(m-2).
```

Then `a^4 = 1`, and for every `r in R`

```text
[e_13(r), a] = e_13(r) e_23(r),
[e_12(1), [e_13(r), a]] = e_13(r).
```

So every elementary generator is a product of at most four conjugates of `a`
or `a^(-1)`, and `a` normally generates `EL_m(R)`.

If `2` is not a zero divisor in `R`, then `a` has order exactly four; in
characteristic two `a` is the unsigned transposition and has order two.
