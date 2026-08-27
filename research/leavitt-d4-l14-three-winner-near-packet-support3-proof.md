---
rg: 2
id: leavitt-d4-l14-three-winner-near-packet-support3-proof
kind: route
title: Replay sparse Leavitt packets through all three carriers and cyclic boundary reduction
target: leavitt-d4-l14-three-winner-near-packet-support3-is-empty
requires:
  - leavitt-d4-l14-three-winner-boundary-needs-21-blocks
---

Start from the exact carrier solution

```text
(p,u,v,w,x,y,z,a,b,c,d,e)
  =(1,S,S,S,1,S,A^-1,A,1,1,1,1),
```

where `A=cd` has order four and `S=c` in the Leavitt unit group.  Its four
copy projections carry the nontrivial mark `A^2`, but its full boundary is
multicopy.  Mutate one, two, or three non-common slots over

```text
{1,A,A^-1,S,a,c,e,r,r^-1,p,p^-1,q,b,d},
```

requiring at least one unit outside the displayed dihedral packet.  Every
library entry is stored with its genuine Bergman-normal-form inverse.  For
each assignment the artifact replays the literal raw corners, demands all
three full carrier equations, and cyclically reduces the free-product
boundary.  Thus it accepts a boundary conjugate into any of the four copies,
not merely a linearly reduced one-copy word.

MSI array `16679438` returned

```text
tested=587574
carrier_solutions=4924
hits=0
```

across all sixteen shards.  Logs are
`msi-l14-3win-packet-16679438_*.out`.  This supersedes the pre-patch array
`16679088`, which tested only literal linear one-copy reduction.  The result
is a bounded support-three fence, not a global obstruction to longer
Leavitt compounds or more changed slots.
