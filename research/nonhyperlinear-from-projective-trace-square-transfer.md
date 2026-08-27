---
rg: 2
id: nonhyperlinear-from-projective-trace-square-transfer
kind: route
title: Projective trace-square transfer makes the co-dense SL3 HNN group non-hyperlinear
target: non-hyperlinear-group
requires:
  - projective-trace-square-transfer-for-sl3-pair
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
---

Let

```text
G = < SL_3(Z[1/2]), t | [t,SL_3(Z)]=1 >
```

and choose `h=diag(2,1,1/2)`.  Britton normal form gives `[t,h]!=e`.
If `G` were hyperlinear, take regular-trace microstates `rho_n` and put
`U_n=rho_n(t)`.  The HNN relators and presentation defect make the right
side of `(PTS1)` tend to zero, so

```text
|tr([rho_n(t),rho_n(h)])| -> 1.
```

But `[t,h]` is a nontrivial group word, and regular-trace microstates require
its trace to tend to zero.  This contradiction proves that `G` is not
hyperlinear.  Notice that no scalar phase is selected or corrected: its
modulus-one trace is already incompatible with the canonical group trace.

