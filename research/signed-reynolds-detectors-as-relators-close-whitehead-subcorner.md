---
rg: 2
id: signed-reynolds-detectors-as-relators-close-whitehead-subcorner
kind: route
title: Eliminate the Reynolds detector branch by relator telescoping and attach the Whitehead subcorner
target: same-center-whitehead-native-selector-subcorner-attachment
requires:
  - same-center-whitehead-analytic-candidate-package
  - paid-t00-carrier-has-signed-hecke-reynolds-dichotomy
---

**INVALIDATED PROPOSAL.**  The proposal was to regard each word

```text
r_g=z^((1-lambda_0(g))/2)g
```

as a bounded-area consequence of the defining presentation.  Vanishing
relator defect would then eliminate the detector branch in `(PSD5)`, forcing
the paid `T/Y` discrepancy into the actual signed source.  One would next
try to use the Whitehead-fixed constant atom and the analytic candidate
package to extract the native unequal-label subcorner.

`signed-reynolds-detectors-form-the-marked-complement-subgroup` invalidates
the first step exactly.  The `r_g` form a faithful subgroup isomorphic to
`L_0`; only `r_1` is the identity.  In the regular representation all
defining relators are exact while every nonidentity detector has operator
norm distance two from the identity, including after compression to the
negative marked sector.  Hence no relator-area estimate can make this menu
small.

This does not invalidate the Reynolds dichotomy itself.  A live continuation
must use the source-compressed discrepancy, prove detector smallness only on
a newly authenticated paid subcorner, or add a genuinely new incidence
relation.  Ordinary presentation telescoping alone cannot attach the native
Whitehead selector rows.
