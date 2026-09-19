---
rg: 2
id: pvm-overlap-polar-matches-large-labeled-carriers
kind: claim
title: PVM overlap polar decomposition matches all but the off-label carrier mass
distinct_from:
  diagonal-sign-margin-controls-hash-overlap: that bounds the off-label overlap from sampled reflection correlations; this converts such overlap into one near-identity labeled partial unitary
  two-code-character-cut-recenters-to-one-coordinate: that aligns one binary spectral cut; this matches an arbitrary finite label menu in one polar decomposition
---

Let `(F_v)` and `(E_v)` be two finite PVMs in one matrix algebra and put

```text
Gamma=sum_(u!=v)tau(E_uF_v)
      =1-sum_vtau(E_vF_v).                              (POM1)
```

There are subprojections `F_v^0<=F_v`, `E_v^0<=E_v` and one partial
isometry `V` such that

```text
V^*V=sum_vF_v^0,          VV^*=sum_vE_v^0,
VF_v^0V^*=E_v^0,                                         (POM2)

tau(1-sum_vF_v^0)<=Gamma,
tau(1-sum_vE_v^0)<=Gamma.                               (POM3)
```

Moreover `V` extends across the discarded equal-trace complements to a
unitary `U`, after an additional carrier of trace at most `2Gamma` is
quarantined if the individual labeled ranks differ, and one may arrange

```text
||U-I||_2^2<=16 Gamma.                                  (POM4)
```

Thus off-label overlap `o(1)` gives one simultaneous polar/Hall matching of
all labeled carriers, with `o(1)` quarantine and one near-identity unitary;
there is no loss proportional to the number of labels.

## Attempts

Matching each label by an arbitrary rank-preserving unitary loses all metric
control.  The block-diagonal overlap operator `A=sum_vE_vF_v` contains all
labels at once.  Its polar decomposition supplies the metric matching, while
the kernel and labeled rank imbalance are already bounded by `(POM1)`.
