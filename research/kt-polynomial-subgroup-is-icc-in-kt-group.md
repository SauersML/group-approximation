---
rg: 2
id: kt-polynomial-subgroup-is-icc-in-kt-group
kind: claim
title: Every nontrivial element of the binary Kun--Thom group has infinite conjugacy class under the polynomial subgroup
distinct_from:
  kt-normalizing-witnesses-centralize-compressors: that uses triviality of the centralizer of the polynomial subgroup; this is the stronger statement that no nontrivial element even has a finite-index centralizer in that subgroup.
---

**ESTABLISHED.** For the binary Kun--Thom Theorem E pair

```text
Gamma = EL_r(F_2[x_1,...,x_d]) <= G = EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),   r,d >= 3,
```

every `h in G - {e}` has infinite `Gamma`-conjugacy class. Equivalently
`C_Gamma(h)` has infinite index in `Gamma` for every `h != e`. The same holds
for every conjugate `t Gamma t^(-1)` contained in `Gamma`.

This is the hypothesis of `fell-models-inherit-walls-from-coefficients`.

DERIVATION
kt-polynomial-subgroup-icc-proof
