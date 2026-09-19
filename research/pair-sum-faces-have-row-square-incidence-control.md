---
rg: 2
id: pair-sum-faces-have-row-square-incidence-control
kind: claim
title: Pair-sum faces have operator row-square incidence control
distinct_from:
  pair-sum-faces-control-shared-commutator-energy: that proves the normalized trace estimate; this retains operator order after a fixed congestion symmetrization.
  fixed-parity-faces-exactify-with-loewner-row-square-control: that constructs exact copies inside each face; this compares those copies with shared representatives over all logical pairs.
---

ESTABLISHED.  In the setting of
`pair-sum-faces-control-shared-commutator-energy`, put
`D_(f,i)=Q_i-A_(f,i)`.  There is a fixed positive symmetrization
`H_inc^sym` of

```text
 H_inc=(1/I)sum_f sum_(i in f)D_(f,i)^2
```

such that

```text
 (1/L^2)sum_(i,j)[Q_i,Q_j]^*[Q_i,Q_j]
 <= C H_inc^sym                                                (PSR1)
```

in Loewner order.  The symmetrization adds only conjugates by the finitely
many endpoint reflection words attached to one bounded face occurrence;
its multiplicity and `C` depend only on the fixed row width and on `M/L`.
Consequently its normalized trace is at most a fixed constant times the
ordinary incidence energy.

This operator inequality does **not** say that `H_inc^sym` is covariant
under the original presentation generators.  The shared endpoint
reflections can be analytic signs of cloud averages rather than group
words.  Thus `(PSR1)` alone does not authorize a new reducing spectral cut.
Its use in the Green-edge argument is after normalized trace, where every
endpoint conjugate has exactly the same trace as its unconjugated square.
