---
rg: 2
id: leavitt-three-winner-five-sectors-fence-proof
kind: route
title: Close the five residual sectors by relator differences
target: leavitt-three-winner-five-sectors-fenced
requires:
  - leavitt-d4-l14-three-winner-profile-has-one-class
---

The exhaustive cyclic-boundary shard audit `16684869` found no free target in
these five sectors.  After direct relators, primitive powers, iterative
primitive-root saturation, and involutory Tietze substitutions, the respective
unresolved counts were `5,5,2,6,4`, for 22 coordinate presentations total.

Every one of the 22 is killed by one exact normal-closure step.  For each
presentation the artifact finds stored relators `r` and `s` such that the
freely reduced word `r s^-1` is a cyclic conjugate of the target or its inverse.
Since `r=s=1`, the target is therefore one.  There are eight distinct exact
certificate pairs among the 22 records.  The most frequent family, occurring
under generator renamings, is

```text
r = b^-2 a b^-1 a^-1,
s = b^-1 a b^-1 a^-1,
r s^-1 = b^-1.
```

The classifier compares in the free group, before any coefficient-group
specialization; this is a nonabelian implication and not a projection screen.
Thus all 22 residual presentations, and hence all five sectors, are fenced.
The eight exact `(q,r,s,r s^-1)` records and their multiplicities are stored in
`research/artifacts/l14-three-winner-relator-difference-certificates.json`.
