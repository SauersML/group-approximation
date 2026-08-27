---
rg: 2
id: steinberg-nonconstant-weights-generate-full-projective-module
kind: claim
title: Every nonconstant Steinberg marginal weight generates the full projective weight module
invalidates:
  - steinberg-marginals-via-small-weighted-transform-closure
artifacts:
  - research/steinberg-weighted-transform-firewall-proof.md
distinct_from:
  steinberg-pushed-marginal-sums-have-no-new-closure: that treats only the constant unweighted sector; this proves that adjoining any nonconstant projective weight expands to every weight rather than to a smaller closed packet.
---

**ESTABLISHED FIREWALL.**  Extend an affine marginal weight by value zero at
infinity.  The pullbacks appearing in the `s` and `u` pushes include

```text
t |-> t+a,                    t |-> t/(1+t).           (SWTF1)
```

They generate `SL_2(F_p)` on `P^1(F_p)`.  In defining characteristic,

```text
F_p[P^1]=F_p*1 direct_sum St_2,                        (SWTF2)
```

where the augmentation summand `St_2` is simple of dimension `p`.  Hence
the orbit of any nonzero zero-sum weight spans all of `St_2`; together with
the already-used constant equation it spans every projective weight.

Therefore there is no proper small weighted Fourier/Radon subsystem between
the constant balances and the full pointwise chord recurrence.  This
invalidates only that proof method, not marginal vanishing itself.

DERIVATION
steinberg-weighted-transform-firewall-proof
