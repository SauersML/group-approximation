---
rg: 2
id: near-full-hecke-quarter-profile-loss-proof
kind: route
title: Count the discarded negative half of the balanced second Hecke sign
target: near-full-hecke-source-cannot-retain-quarter-native-profile
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
---

Put

```text
Q_-=Q(1-t)/2.
```

The four-sector theorem gives `tau(Q_-)=q/2`.  For an arbitrary projection
`E<=Q`, traciality gives

```text
tau(EQ_-E)=tau(EQ_-),
q/2-tau(EQ_-E)=tau((Q-E)Q_-)
                  =tau((Q-E)Q_-(Q-E)).
```

The last operator is positive and bounded above by `Q-E`.  Hence

```text
q/2-tau(EQ_-E)<=eta.                                  (1)
```

If `rho=1/4`, then `tau(EQ_-E)=beta/4=(q-eta)/4`.
Substitution in `(1)` gives

```text
q/2-(q-eta)/4<=eta,
q<=3eta,                                               (2)
```

which is `(QPL3)`.

For the robust statement, `|rho-1/4|<=zeta` implies

```text
tau(EQ_-E)=rho beta<=(1/4+zeta)(q-eta).               (3)
```

Combining `(1)` and `(3)` yields

```text
q/2-(1/4+zeta)(q-eta)<=eta,
(1/4-zeta)q<=(3/4-zeta)eta.                           (4)
```

Division by the positive number `(3/4-zeta)q` proves `(QPL4)`.

Sharpness of `(QPL3)` follows whenever the balanced negative sector admits
a one-third subprojection, after harmless finite amplification if needed:
take `E` to contain the whole positive sector and one third of the negative
sector.  Then `beta=2q/3`, `tau(EQ_-E)=q/6=beta/4`, and `eta=q/3`.

Finally, the common-source theorem gives

```text
q=tau(Q)=1/(64*2^7)=1/8192,
```

so `(QPL5)` is `q/3=1/24576`.
