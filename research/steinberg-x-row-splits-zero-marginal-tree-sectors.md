---
rg: 2
id: steinberg-x-row-splits-zero-marginal-tree-sectors
kind: claim
title: The X row splits zero-marginal circulations across disjoint tree sectors
artifacts:
  - research/steinberg-x-tree-sector-split-proof.md
distinct_from:
  steinberg-zero-marginal-space-is-biaffine-circulation: that identifies the ambient circulation space; this extracts new slice equations from the X recurrence on that space.
  steinberg-zero-marginal-fox-recurrence-is-zero: this proves necessary slice identities and a vanishing line, but not yet that the entire circulation is zero.
---

**ESTABLISHED.**  Suppose `F=E_p f` has `P_f=H_f=0` and `XF=0`.  Put

```text
delta_q=(1-q)F,             delta_s=(1-s)F.
```

Then the equation `XF=0` is the noncancelling decomposition

```text
F=A delta_q+B delta_s,                                  (SXTS1)
```

where each summand separately has zero tree coefficients and hence has
zero point and plane marginals.  The exceptional source slices therefore
satisfy

```text
f(-1/2,b,c)=f(0,b,c),
f(a,b,-1/2)=f(a,b+a/2,0)                               (SXTS2)
```

for all coordinates.  Moreover the chord part of `A delta_q` vanishes on
the target hyperplane `a=1/2`, while that of `B delta_s` vanishes on `c=1`.
In particular

```text
f(1/2,b,1)=0                                            (SXTS3)
```

for every `b`.

DERIVATION
steinberg-x-tree-sector-split-proof
