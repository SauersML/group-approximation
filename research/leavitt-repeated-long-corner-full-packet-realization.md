---
rg: 2
id: leavitt-repeated-long-corner-full-packet-realization
kind: claim
title: Realize the repeated long-corner transport with a full Leavitt packet
artifacts:
  - research/artifacts/search-leavitt-repeated-long-corner-radius2.py
  - research/artifacts/search-leavitt-repeated-long-corner-radius2.sbatch
refuted_by: leavitt-repeated-long-corner-gate-count-obstruction
---

Find coefficients `g_0,g_1,g_4,g_7` in the binary Leavitt elementary group
such that, with

```text
g_2=a,   g_3=c,   g_5=b,   g_6=d,
```

the three long Reidemeister--Schreier corners for signs `++-++-++` satisfy
`H=L=N`, and the eight coefficients generate the full group.  This would
turn `leavitt-repeated-long-corner-template-kills-omega` into an explicit
nonhyperlinear group witness.

## Attempts

The identity-gate formal assignment `(x,x,1,1,x,1,1,x)` proves that the
cyclic incidence permits the collision.  Fixing the four actual gates and
choosing each remaining slot among all 82 distinct canonical packet words of
radius at most two gives no solution in `45,212,176` exact layouts (MSI job
`16659733`).  The subsequent syllable-count argument proves that increasing
the compound radius cannot help in this fixed slot placement.
