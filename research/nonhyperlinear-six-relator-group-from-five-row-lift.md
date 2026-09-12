---
rg: 2
id: nonhyperlinear-six-relator-group-from-five-row-lift
kind: route
title: The five-row phase lift directly makes the six-relator Atlas quotient nonhyperlinear
target: non-hyperlinear-group
requires:
  - atlas-five-row-operator-phase-lift
  - atlas-six-relator-hyperlinear-escape-test
---

The group

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>
```

is finitely presented.  By
`atlas-six-relator-hyperlinear-escape-test`, if it
were hyperlinear then its canonical-trace microstates, exactified on the two
finite factors, would give a regular common-orbit sequence with all six
nonlinear defects tending to zero and five-row additive energy bounded away
from zero.  The multiplicity-independent inequality in
`atlas-five-row-operator-phase-lift` forces that additive energy to tend to
zero.  This contradiction proves that `Gamma_6` is nonhyperlinear.
