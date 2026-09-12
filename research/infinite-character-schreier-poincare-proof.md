---
rg: 2
id: infinite-character-schreier-poincare-proof
kind: route
title: Apply counting-measure Poincare to the finitely supported rank vector
target: one-seed-infinite-character-expansion-collapses-mark
requires: []
---

Put `f(chi)=sqrt(tr_d(P_chi))`.  Only finitely many `P_chi` are nonzero in a
finite-dimensional representation, so `f in ell^2(Omega)` and

```text
sum_chi f(chi)^2=mu_1.
```

The projection estimate from the proof of
`expander-pvm-transport-forces-dimension-or-mass-collapse` and `(ISC1)` give

```text
E_act
 >=(1/|S|) sum_(s,chi)|f(chi)-f(s chi)|^2
 =2 <f,(I-M)f>
 >=2 gamma mu_1.                                              (1)
```

The seed trace calculation `(3)--(4)` in
`one-seed-character-expansion-proof` gives

```text
mu_1 >= mu/2-sqrt(mu)eta_seed/4.                              (2)
```

Combine `(1)--(2)` and use
`sqrt(mu)eta_seed/4<=mu/4+eta_seed^2/16`.  This yields

```text
mu/4 <= E_act/(2 gamma)+eta_seed^2/16,
```

which is `(ISC3)`.
