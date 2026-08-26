---
rg: 2
id: steinberg-y-propagates-matching-to-zero-families
kind: claim
title: The Y row propagates the X matching zeros to a full fiber and two transverse lines
artifacts:
  - research/steinberg-y-zero-family-propagation-proof.md
distinct_from:
  steinberg-x-row-splits-zero-marginal-tree-sectors: that obtains the first matching zeros from X; this uses Y and the zero marginals to propagate them to three larger zero families.
---

**ESTABLISHED.**  Suppose `P_f=H_f=0` and both Steinberg chord Fox rows
vanish.  In addition to `(SXTS3)`, one has

```text
f(-1/4,B,-1)=0                 for every B,            (SYZ1)
f(-1/4,0,t)=0                  for every t,             (SYZ2)
f(a,a+1/4,1)=0                 for every a.             (SYZ3)
```

More generally, before summing the marginals, the exact propagation law is

```text
f(-1/4,B,t)=f(B-1/4,B,t/(1+t))       when t!=-1.       (SYZ4)
```

All exceptional terms used here are zero tree coefficients, so the result
holds uniformly for every odd prime, including `p=3`.

DERIVATION
steinberg-y-zero-family-propagation-proof
