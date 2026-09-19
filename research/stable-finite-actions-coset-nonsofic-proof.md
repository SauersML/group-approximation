---
rg: 2
id: stable-finite-actions-coset-nonsofic-proof
kind: route
title: Make the orbit atlas sofic by residual amplification and invoke weak containment
target: stable-finite-actions-blocks-codense-kazhdan-coset-soficity
requires:
  - codense-kazhdan-coset-action-forces-permutation-outliers
---

Assume `(SFA1)` is sofic.  Exhaust `A` and `A/C` by finite windows and choose
orbit approximations

```text
alpha_n : A -> Sym(V_n),             epsilon_n -> 0.             (SFA2)
```

Residual finiteness supplies finite quotients `q_n:A->Q_n` which are
injective on the `n`-th actor window.  On `V_n x Q_n` put

```text
theta_n(a)(v,x)=(alpha_n(a)v, q_n(a)x).                           (SFA3)
```

The multiplication defect of `theta_n` is the defect of `alpha_n`, while
the regular `Q_n` coordinate makes every tested nonidentity element
fixed-point-free.  Hence `theta_n` is a sofic approximation of `A`.  Pull
the orbit-atlas labels in `(SFA2)` back along the first-coordinate map
`V_n x Q_n -> V_n`; all normalized partition intersections and covariance
errors are unchanged.

Let `beta` be the ultraproduct p.m.p. action of `(SFA3)`.  The pulled-back
labels give in `beta` the limiting two-site atlas: its base label is
`C`-invariant, while the label transported by a fixed `h in A\C` is disjoint
in the orbit-atlas sense.  Since `A` is stable in finite actions, `beta` is
weakly contained in the family of finite `A`-actions.  Weak containment of
a finite partition says that, for every positive tolerance, the finitely
many measures of intersections of its translates can be reproduced in one
genuine finite action.  Applied to the Kazhdan set of `C`, `h`, and the two
atlas labels, this gives exact finite-action orbit atlases with error tending
to zero.

But `codense-kazhdan-coset-action-forces-permutation-outliers` gives the
uniform lower bound

```text
kappa^2/(2 kappa^2+8)>0
```

for those exact atlases.  This contradiction proves `(SFA1)` nonsofic.

The residual amplification `(SFA3)` is elementary; it is also Lemma 3.2 of
Alekseev--Thom, arXiv:2512.15494, whose current primary text was checked in
`alekseev-thom-stability-finite-actions-boundary`.
