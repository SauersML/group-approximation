---
rg: 2
id: isolated-rstar-context-determinizes-to-a-fano-cap
kind: claim
title: One isolated R-star context determinizes over either retained fibre into a Fano cap
distinct_from:
  rstar-private-tail-fiberwise-cap-collapse: that applies the construction simultaneously in an instance under occurrence-privacy; this is the unconditional one-context operator lemma before any shared-auxiliary compatibility question.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for one globally compatible choice in every occurrence of the published shared-variable gadget; this proves only the isolated local selection.
  rstar-cap-support-is-one-character-row: that characterizes a support which is already cap-contained; this constructs such a support by replacing three observables inside one context.
---

**ESTABLISHED ISOLATED-CONTEXT LEMMA.**  After translating the excluded
ghost, write

```text
R_*={(x_1,t):t=(x_2,x_3,x_4) in F_2^3 minus {0},
                  x_1+x_2+x_3+x_4=1}.                 (IRC1)
```

Let `A_1,...,A_4` be commuting involutions giving a perfect representation
of this one context, and put

```text
P_a=(1+(-1)^a A_1)/2,             a in F_2.           (IRC2)
```

For every active fibre `P_a!=0`, choose one positive joint atom
`(a,u_a) in R_*`.  Define, for `j=2,3,4`,

```text
Ahat_j=sum_(a:P_a!=0) (-1)^((u_a)_j) P_a.             (IRC3)
```

Then `Ahat_j in W^*(A_1)`, the four resulting observables commute, and

```text
A_1 Ahat_2 Ahat_3 Ahat_4=-I.                          (IRC4)
```

Their positive support contains at most the two selected atoms.  If both
fibres are active then `u_0!=u_1`, because the odd-parity equation determines
`x_1` from `t`; two distinct nonzero vectors of `F_2^3` are linearly
independent.  Hence the simultaneous equations

```text
lambda dot u_a=1                  for every active a   (IRC5)
```

have a nonzero solution `lambda in F_2^3`.  Spectral evaluation of `(IRC3)`
therefore gives the exact character identity

```text
Ahat_2^(lambda_2) Ahat_3^(lambda_3)
 Ahat_4^(lambda_4)=-I.                                 (IRC6)
```

Thus the selected local support lies in the maximal four-point cap

```text
C_lambda={t:lambda dot t=1}.                           (IRC7)
```

No privacy hypothesis is needed for this one-context conclusion.  Privacy
or another global compatibility mechanism is needed before the replacements
in `(IRC3)` may be made simultaneously in a multi-occurrence pp-gadget.
