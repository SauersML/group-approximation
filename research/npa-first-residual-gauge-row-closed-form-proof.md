---
rg: 2
id: npa-first-residual-gauge-row-closed-form-proof
kind: route
title: Expand the four cross terms and check the two word reductions
target: npa-first-residual-gauge-row-closed-form
requires:
  - pakhunov-critical-face-structural-laws
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Write `p = ((0), r_(k-2))` and `q = ((0), r_(k-1))`, both level-`k` basis words
since `1 + (k-2) <= k` and `1 + (k-1) <= k`.  Deleting the trailing `0` on the
first party gives

```text
T_p = e_[((0), r_(k-2))] - e_[(empty, r_(k-2))],
T_q = e_[((0), r_(k-1))] - e_[(empty, r_(k-1))].
```

The pairing expands into four terms `+ p*q`, `- p*q'`, `- p'*q`, `+ p'*q'` with
`p' = (empty, r_(k-2))`, `q' = (empty, r_(k-1))`.  Two reductions settle all
four.

*Party A.*  The four A-side words are `rev(0).0 = 00`, `rev(0).empty = (0)`,
`empty.0 = (0)`, and `empty`.  The first collapses to the identity, so the four
A-sides are `empty`, `(0)`, `(0)`, `empty`.

*Party B.*  Every term has B-side `rev(r_(k-2)) . r_(k-1)`.  Reversal sends
`r_(k-2)` to an alternating word whose last letter is `r_(k-2)[0]`, of parity
`k-2 mod 2`, while `r_(k-1)` opens with a letter of parity `k-1 mod 2`.  The two
parities differ, so the juncture neither cancels nor repeats: the concatenation
is alternating of length `(k-2) + (k-1) = 2k-3` and ends in `1`, i.e. it is
`r_(2k-3)`.

Collecting with signs gives `+ y_[(empty, r_(2k-3))] - y_[((0), r_(2k-3))]
- y_[((0), r_(2k-3))] + y_[(empty, r_(2k-3))]`, which is the stated `A_k`.

Both relations are columns of `N_k`, so `A_k` is a genuine entry of
`Phi_k(y) = N_k^T Gamma_k(y) N_k` and hence a row of the level-`k` system.  Its
support has degree `2k-3 <= 2k-2`, so it is an old-class row.  Comparison with
the imported germ step identifies it as twice that step's first residual
condition.
