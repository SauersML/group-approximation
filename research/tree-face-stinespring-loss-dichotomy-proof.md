---
rg: 2
id: tree-face-stinespring-loss-dichotomy-proof
kind: route
title: Bound finite-face multiplication by the diagonal Kadison--Schwarz slack
target: tree-face-balance-pays-stinespring-loss-or-word-distance
requires:
  - tree-face-balance-pays-word-or-multiplicative-defect
---

Choose a Stinespring representation

```text
Phi(x)=W^* pi(x)W,       W^*W=1,       P=WW^*.
```

For `g,h` in one tree face `V`, the Stinespring corner identity gives

```text
Phi(u_(gh))-Phi(u_g)Phi(u_h)
 =W^* pi(u_g)(1-P)pi(u_h)W.                               (1)
```

All factors on the left of `(1-P)pi(u_h)W` are contractions.  Hence

```text
||Phi(u_(gh))-Phi(u_g)Phi(u_h)||
 <=||(1-P)pi(u_h)W||
 =||W^*pi(u_h)^*(1-P)pi(u_h)W||^(1/2)
 =||1-Phi(u_h)^*Phi(u_h)||^(1/2)
 <=sqrt(sigma_V).                                         (2)
```

Taking the maximum gives `mu_V<=sqrt(sigma_V)`.  The established word-or-
multiplication dichotomy supplies a face `V` with

```text
mu_V+3 gamma_V>=delta_L.
```

Equation `(2)` proves `(SMD2)`.  If both alternatives in `(SMD3)` failed on
that face, then `sqrt(sigma_V)<delta_L/2` and
`3 gamma_V<delta_L/2`, contradicting `(SMD2)`.  Finally

```text
1-Phi(u_g)^*Phi(u_g)
 =W^*pi(u_g)^*(1-P)pi(u_g)W,
```

whose norm is `||(1-P)pi(u_g)W||^2`; this proves `(SMD4)`.
