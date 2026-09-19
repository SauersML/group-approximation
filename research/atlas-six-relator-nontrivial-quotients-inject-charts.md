---
rg: 2
id: atlas-six-relator-nontrivial-quotients-inject-charts
kind: claim
title: Every nontrivial quotient of the six-relator group injects both marked A8 charts
distinct_from:
  atlas-six-relator-finite-escape-is-simple-test: that proves the assertion only en route to a maximal finite simple quotient and then classifies finite escapes; this removes every finiteness and linearity hypothesis.
  atlas-six-relator-hyperlinear-escape-test: that characterizes matrix-ultraproduct escapes by hyperlinear quotients; this is the purely algebraic quotient rigidity which reduces its hyperlinear quotient condition to nontriviality.
  atlas-six-relator-quotient-identifies-h-bridge: that falsely claimed the two marked H subgroups agree in the six-relator quotient; this says instead that neither whole A8 chart can disappear in any nontrivial quotient.
---

**ESTABLISHED.**  For

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>,
```

every homomorphism

```text
q:Gamma_6 -> Lambda
```

has exactly two possibilities:

```text
q is trivial,
```

or both restrictions

```text
q|_(A8_1), q|_(A8_2)
```

are injective.  No assumption on `Lambda` is needed.

Consequently `Gamma_6` has a nontrivial hyperlinear quotient if and only if
it has a hyperlinear quotient injecting both marked charts.  Combined with
`atlas-six-relator-hyperlinear-escape-test`, this says that the remaining
qualitative five-row assertion is exactly

```text
Gamma_6 has no nontrivial hyperlinear quotient.          (NQI1)
```

This is stronger than merely saying that `Gamma_6` is nonhyperlinear: every
nontrivial quotient must be nonhyperlinear.

