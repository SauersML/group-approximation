---
rg: 2
id: y-square-coarea-has-a-compatible-hard-soft-window
kind: claim
title: The Y-squared coarea threshold has a nonempty hard-reset and soft-contraction window
distinct_from:
  hard-soft-exponent-conflict-is-a-norm-mismatch: that corrects the abstract amplitude ledger for a cutoff on Y; this translates the actual spectral cutoff on R=Y squared, including its coarea boundary scale.
  one-anchor-odd-spike-has-a-cheap-reducing-cut: that proves the exact one-spike cut estimates; this chooses an energy-dependent threshold and compares all resulting scales with anchor contraction.
  central-adaptive-peeling-or-noncentral-stopping: that must sum many overlapping cuts; this proves only that no exponent obstruction prevents such a stopping selection.
---

Put `E=(1/L)sum_i q_i^2` and consider one pair `(a,i)` at the RMS
scales

```text
q_a+q_i<=C_0 sqrt(E),
||[Q_a,Q_i]||_2^2<=C_1 E.                              (YSC1)
```

Apply `one-anchor-odd-spike-has-a-cheap-reducing-cut` to
`R=Y_(a,i)^2` with spectral threshold `s=E^beta`, where

```text
0<beta<1/2.                                             (YSC2)
```

Then its three relevant scales are

```text
high-block trace       <=(C_1/4) E^(1-beta),
reducing-boundary cost <=2C_0 E^(1/2-beta),
soft odd norm          <=sqrt(2) E^(beta/2).            (YSC3)
```

All tend to zero.  In particular the quadratic anchor remainder is at most
`O(E^(beta/2))` times residual amplitude.  If the linear anchor step
contracts amplitude by `theta<1`, the corrected recurrence is

```text
sqrt(E_new)
 <=(theta+C E^(beta/2))sqrt(E),                         (YSC4)
```

which is a strict contraction for all sufficiently small `E`.

Thus the actual `R=Y^2` coarea threshold reinforces, rather than spoils,
the correction in `hard-soft-exponent-conflict-is-a-norm-mismatch`.
The earlier incompatible-exponent conclusion is not resurrected by the
square root between `R` and `Y`.

The scope is local and exact.  Averaging shows that RMS-scale rows and
pairs exist in abundance, but independently cutting all such pairs may
charge the same commutator row `Theta(L)` times.  Therefore `(YSC3)` does
not establish global centralization.  It removes the last scalar exponent
objection and leaves precisely the disjoint-mass/geometric-decay selection
in `central-adaptive-peeling-or-noncentral-stopping`.

