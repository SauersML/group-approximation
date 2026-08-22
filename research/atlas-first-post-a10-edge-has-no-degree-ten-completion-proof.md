---
rg: 2
id: atlas-first-post-a10-edge-has-no-degree-ten-completion-proof
kind: route
title: Exhaust every involution in S10 against the first cycle relations
target: atlas-first-post-a10-edge-has-no-degree-ten-completion
requires:
  - atlas-forward-collision-has-faithful-a10-quotient
  - atlas-first-post-a10-core-edge-is-a-centralizer-double-coset
---

Use the five explicit permutations `r,z,c,t,s` from the faithful A10
certificate.  The missing first-chart label `u` is the involution `s` in the
other `S3` factor of the local `S3 x S3` packet.  Therefore its exact
relations with `F=<r,z,c>` are

```text
u^2=1,       u r u=r^-1,       [u,z]=[u,c]=1.         (S10-1)
```

The next core context pairs `u` with the second-chart `t^-1`; allowing both
orientations amounts to testing

```text
(u t)^3=1       or       (u t^-1)^3=1.                (S10-2)
```

The artifact first closes the given five permutations and independently
recovers all `1814400` elements of `A10`.  It then enumerates the complete
`10!=3628800` tuple list for `S10`.  For every tuple it checks `(S10-1)` and
both equations in `(S10-2)` by exact permutation composition.  The candidate
count is zero in A10 and remains zero in S10.

This is a complete degree-ten statement.  It does not exclude an involution
in a larger finite overgroup or in the 288-point regular `J` block isolated
by the centralizer reduction.
