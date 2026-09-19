---
rg: 2
id: finite-regular-adjoint-retains-full-conductor
kind: claim
title: The adjoint of a finite regular representation retains the full quotient conductor
distinct_from:
  projective-commutant-transfer-for-arithmetic-pair: that seeks a transfer modulus for arbitrary approximate arithmetic representations; this is the exact finite-quotient obstruction showing adjoint lifting does not erase congruence depth.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that localizes approximate SL3 leaks in the dyadic tower; this proves the regular adjoint functor preserves every exact level of that tower.
---

For every finite group `Q`, conjugation on Hilbert--Schmidt operators in the
left regular representation satisfies

```text
Ad(lambda_Q) ~= direct_sum_(1)^|Q| lambda_Q.          (FRA1)
```

In particular it is faithful, and for every `g!=1`,

```text
||Ad(lambda_Q(g))-1||_(2,|Q|^2)=sqrt(2).              (FRA2)
```

Consequently, for `Q_a=SL_3(Z/2^a Z)` and every nontrivial element of a
reduction kernel `ker(Q_a->Q_b)`, `b<a`, its regular adjoint image remains
nontrivial and at normalized Hilbert--Schmidt distance `sqrt(2)` from the
identity.  Passing to adjoint lifts removes scalar projective cocycles but
does not lower the dyadic conductor or collapse the depth-two tower.
