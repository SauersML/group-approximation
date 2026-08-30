---
rg: 2
id: stw99-xciv-commutant-capacious-radius-proof
kind: route
title: Centralize the approximating core and pay twice its operator-norm error
target: stw99-xciv-commutant-capacious-radius-controls-block-defect
requires:
  - stw99-xciv-finite-dimensional-radius-controls-block-defect
artifacts:
  - research/artifacts/stw99-xciv-commutant-capacity-audit-2026-08-30.md
---

Let `A subset R` be D-capacious and choose a unital

```text
psi:D->A' intersect R.
```

For `a in F`, choose `b_a in A`.  Since `psi(h)` commutes with `b_a` and
every `h` in the fixed generating set is contractive,

```text
||[a,psi(h)]||
 =||[a-b_a,psi(h)]||
 <=2||a-b_a||.                                          (7)
```

Take the maximum over `F` and the generators, then infimize first over the
`b_a` and finally over D-capacious `A`.  This proves `(4)`.  Its
contrapositive is `(6)`.

Every unital finite-dimensional `E subset R` is D-capacious by
`stw99-xciv-relative-ii1-commutant-block-proof`, so `beta_D(F)<=alpha_R(F)`.
This recovers the earlier bound but does not reduce to it.

For a tensor decomposition `R=R_0 tensor_bar R_1`, the relative commutant of
`R_0 tensor 1` contains `1 tensor R_1`, and every II1 factor contains a
unital copy of `D`.  Thus the first leg is D-capacious, proving `(5)`; the
other leg is symmetric.  All distances and estimates are in operator norm.
