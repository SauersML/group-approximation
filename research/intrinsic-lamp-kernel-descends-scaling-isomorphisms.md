---
rg: 2
id: intrinsic-lamp-kernel-descends-scaling-isomorphisms
kind: route
title: Descend a scaling-family isomorphism to its telescope quotient
target: scaling-family-pairwise-nonisomorphic
requires:
  - scaling-lamp-kernel-isomorphism-invariant
  - scaling-skeleton-quotients-pairwise-nonisomorphic
---

If `Phi:E_m->E_n` is an isomorphism, the first prerequisite gives
`Phi(N_m)=N_n`, so `Phi` descends to

```text
E_m/N_m ~= E_n/N_n.
```

The second prerequisite identifies these quotients with `V_m,V_n` and
recovers the scale from

```text
|Tor(Rad_am(V_m)^ab)|=(m-1)^3.
```

Hence `m=n`.
