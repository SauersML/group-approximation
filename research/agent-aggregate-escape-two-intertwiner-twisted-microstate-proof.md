---
rg: 2
id: agent-aggregate-escape-two-intertwiner-twisted-microstate-proof
kind: route
title: Tensor twisted microstates with packet implementers and induce the finite type orbit
target: agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce
requires:
  - agent-aggregate-escape-two-intertwiner-clifford-dichotomy
  - twisted-factor-existence-is-equivalent-to-nonhyperlinearity
  - thom-central-corner-criterion
---

Connes embeddability of `(TNC1)` supplies, on every fixed finite word set,
unitary matrices `M_q^(n)` satisfying

```text
M_q^(n) M_r^(n)
  =omega(q,r)^(-1) M_(qr)^(n)+o_2(1),                  (1)
```

with the twisted regular moments.  On the `sigma` packet space, the chosen
intertwiners satisfy

```text
V_q V_r=omega(q,r)V_(qr).                              (2)
```

Therefore `V_q tensor M_q^(n)` is asymptotically multiplicative with the
ordinary multiplier.  Induction over the finite set `Q/Q_sigma` adds only a
fixed number of blocks and converts the stabilizer tuple into a tuple for
the whole covariance presentation.  Every full relator defect is bounded by
a fixed constant times the maximum defect in `(1)`.

The projection `T e_i` lies entirely in the exact finite packet factor.  At
least the induced identity-coset block contains `sigma`, so its normalized
trace is bounded below by

```text
dim(sigma)/(|Q:Q_sigma| dim(packet orbit sum))
  times tr_sigma(T e_i)>0.                              (3)
```

This constant is independent of the dimensions of the matrices in `(1)`.
Equations `(1)--(3)` contradict `(ACO4)`, proving non-embeddability of
`(TNC1)`.  The cited twisted-factor equivalence and central-corner criterion
give the final interpretation.

