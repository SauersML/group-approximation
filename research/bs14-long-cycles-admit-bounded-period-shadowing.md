---
rg: 2
id: bs14-long-cycles-admit-bounded-period-shadowing
kind: claim
title: Exact BS(1,4) representations admit same-dimensional bounded-cycle Hilbert--Schmidt truncations
artifacts:
  - research/artifacts/bs14-bounded-cycle-shadowing-2026-08-22.md
  - experiments/bs14_bounded_cycle_shadowing_check.py
distinct_from:
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies exact packets and leaves their orbit lengths arbitrary; this proves that long packets can be cut into uniformly short exact packets at quantified normalized-Hilbert--Schmidt cost and without adding dimensions.
  long-cycles-have-unbounded-l2-coboundary-inverse: that measures the inverse loss on one fixed long cyclic shift; this shows that the long cycle itself may first be replaced by short exact BS packets with cost tending to zero.
  direct-sum-weil-compressions-have-quadratic-padding: that repairs compressed Weil blocks by adding dimensions; this is a same-dimensional perturbation internal to exact BS(1,4) representations.
---

Let `R,S in U(d)` satisfy

```text
R S R^(-1)=S^4.                                      (BCT1)
```

For every integer `K>=2` there are `R_K,S_K in U(d)` satisfying the same
relation exactly such that every fourth-power orbit in `spec(S_K)` has length
at most `K` and

```text
||R-R_K||_2^2 <= 8/K,
||S-S_K||_2^2 <= 2 pi^2/(9K).                         (BCT2)
```

Here `||.||_2` is the normalized Hilbert--Schmidt norm on `M_d(C)`.  The
construction preserves the matrix dimension, leaves every original orbit of
length at most `K` unchanged, and replaces each longer orbit only by periodic
fourth-power orbits of lengths at most `K`.  In particular the new base still
has finite odd order.

The theorem removes unbounded fourth-power orbit length as an intrinsic
feature of a finite-dimensional exact `BS(1,4)` skeleton: for any prescribed
period cap it can be imposed at `O(K^(-1/2))` normalized-Hilbert--Schmidt
cost.  Continuous scalar monodromy and compatibility with the extra modular
involution are separate coordinates and are not asserted to be repaired by
this truncation.
