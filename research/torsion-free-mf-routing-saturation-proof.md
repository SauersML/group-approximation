---
rg: 2
id: torsion-free-mf-routing-saturation-proof
kind: route
title: Push the radical word forward and use normality in every quotient
target: torsion-free-mf-radical-routing-saturation
requires:
  - mf-radical-functoriality
---

MF-radical functoriality applied to `q` gives

```text
q(Rad_MF(E)) <= Rad_MF(Q).
```

Hence `(TFR1)` puts `q(d)` in `Rad_MF(Q)`.  The MF radical is normal, so it
contains `normalClosure_Q(q(d))=Q`, proving `(TFR2)`.  The survival clause
`q(d)!=1` makes `Q` nontrivial.

For a nontrivial quotient `pi:Q->>L`, functoriality again gives

```text
pi(Rad_MF(Q)) <= Rad_MF(L).
```

The left side is `pi(Q)=L`, so `Rad_MF(L)=L`.  All finiteness, torsion, and
acylindrical-hyperbolicity clauses are hypotheses on the supplied `Q`, not
analytic consequences, and require no further argument.
