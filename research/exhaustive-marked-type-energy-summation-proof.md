---
rg: 2
id: exhaustive-marked-type-energy-summation-proof
kind: route
title: Sum typewise row defects over orthogonal marked isotypic domains
target: exhaustive-marked-type-energy-summation
requires: []
---

Exactify the fixed finite packet and decompose its marked projection as

```text
Q=sum_lambda Q_lambda.
```

For each fixed test word `r`, orthogonality of the domain projections gives

```text
sum_(lambda:r in T_lambda)||(r-1)Q_lambda||_2^2
 <=||(r-1)Q||_2^2<=||r-1||_2^2.
```

Sum this inequality over the finite union of test words and then insert the
typewise lower bounds.  The forbidden projection commutes with the central
type projections, so its traces add.  Taking the minimum of the finitely
many positive type constants proves the global estimate.  Fixed finite-group
exactification and fixed-word telescoping contribute only the sum of finitely
many dimension-independent error moduli.
