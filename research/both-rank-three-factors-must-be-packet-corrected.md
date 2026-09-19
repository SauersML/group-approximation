---
rg: 2
id: both-rank-three-factors-must-be-packet-corrected
kind: claim
title: Both rank-three corner factors must be corrected and the first live packet equation has two conjugators
distinct_from:
  single-conjugated-s3-packet-correction-equation: that proves every correction confined to the left factor fails; this gives the symmetric obstruction and writes the first equation surviving both.
  leavitt-recursive-kernel-idempotents: that corrects through a nested locally finite tower; this uses two independent conjugates of one fixed three-term kernel packet and no recursion.
  leavitt-corner-one-sided-lift-exists: that permits arbitrary corner corrections; this pins the minimal correction architecture forced on the explicit rank-three pair.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

Let `A=e t~e`, `B=e s~e`, `Delta=AB+e`, and
`P_x=e[x]k[x^-1]e` for the constant `S_3` kernel relation `k`.  Correcting
only one factor can never give a one-sided inverse: `A` and `B` separately
have no ambient one-sided inverse by support localization to their virtually
free support groups.  Correcting both gives

```text
(A+P_x)(B+P_y)=e
```

if and only if

```text
A P_y + P_x B + P_x P_y=Delta.
```

This is the first conjugated-packet equation not already excluded by the
fixed-factor obstruction.  A solution would be a direct-finiteness witness,
because the reverse product evaluates to `s_0t_0!=1`.

## Attempts

Taking either packet zero reduces to a forbidden one-sided inverse for the
other fixed rank-three factor.  No explicit pair `(x,y)` solving the full
bilinear equation is currently known.

