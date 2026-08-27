---
rg: 2
id: atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test
kind: claim
title: The next C144 attachment is an explicit six-generator finite-vertex test
artifacts:
  - experiments/atlas_a4_q96_c144_cycle_low_index.g
  - research/artifacts/atlas-a4-q96-c144-cycle-screen.json
distinct_from:
  atlas-forward-core-triangle-has-faithful-q96-completion: that proves the three-edge triangle is a faithful finite group; this closes the 144-state forward vertex simultaneously along two separated marked subgroups.
  atlas-forward-collision-bass-serre-reduction: that attaches the same 144-state vertex before the noncentral core triangle is imposed; this gives the exact post-Q96 cycle presentation and finite-image test.
---

The first cycle which remains after the faithful `Q96` completion has six
generators.  Put `b=st` and

```text
q=t c s c t^-1 c s t c.
```

The exact universal presentation is the union of the four marked finite
vertices

```text
F'=<r,z,c,u> ~= S3 x S3,       |F'|=36,
Q=<c,u,t>    ~= Q96,            |Q|=96,
J=<t,s,c>    ~= S4,             |J|=24,
C=<r,z,b>    ~= C2^4:C3^2,      |C|=144.               (Q96-C-1)
```

Explicitly its relators are

```text
r^3=z^3=c^2=u^2=t^3=s^2=1,
[r,z]=[c,r]=(cz)^2=(ur)^2=[u,z]=[u,c]=1,
(st)^2=(ct)^3=(ut)^3=q=1,
(r^-1 st)^3=(zst)^3=1.                                (Q96-C-2)
```

Thus the exact binary question is finite and checkable: does `(Q96-C-2)`
have a finite permutation quotient in which the four marked subgroups in
`(Q96-C-1)` retain orders `36,96,24,144`?  Such a quotient is the first
noncentral forward/core carrier through this cycle.  Collapse of any marked
vertex in every finite quotient would be the corresponding finite-model
obstruction.

Two bounded MSI probes are recorded only as run status.  Direct order
enumeration ran for 180 seconds, repeatedly enlarged its coset table, and
timed out.  A separate low-index screen through degree sixteen ran for 120
seconds and timed out before returning a subgroup list.  Neither run proves
that the universal group is infinite, nor that no quotient exists in the
screened degree range.

The target-specific calculation
`atlas-q96-c144-cycle-has-faithful-a8-quotient` subsequently solves the
binary test positively: four `A8` quotient classes preserve all four vertex
orders.  The timeout record remains here only to distinguish generic coset
enumeration from that decisive finite-target search.
