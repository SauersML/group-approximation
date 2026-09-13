---
rg: 2
id: opposite-transvection-slice-is-relatively-embeddable
kind: claim
title: The opposite-transvection Kun--Thom slice inclusion L(Gamma) < L(P) is relatively embeddable over the scalars
distinct_from:
  opposite-transvection-slice-is-not-relatively-embeddable: that is the negative polarity, for some parameters; this is the positive polarity, for all parameters
  heisenberg-kun-thom-slice-is-relatively-embeddable: that proves RE/C for the Ore Heisenberg slice; this is the non-Ore opposite slice
  kt-q2-double-hyperlinear-iff-relative-embeddable: that is the full vertex group G; this is its opposite-transvection subgroup P, and RE/C for G implies it
---

**OPEN.**  For every prime power `q` and all `r,d>=3`, the inclusion
`L(Gamma) subset L(P)` of the opposite-transvection slice is `RE/C`.
Equivalently, by (OTG3) of `opposite-transvections-are-first-nonore-relative-gate`,
`P *_Gamma P` is hyperlinear.

It follows from a sofic coset action.  It implies `RE/C` for the
function-field Hecke pair.  `RE/C` for the Kun--Thom pair implies it
(`kt-double-hyperlinearity-requires-function-field-hecke-re`).

## Attempts

A sofic coset action would suffice (see the routes).  No hyperlinear model
of `P *_Gamma P` that avoids soficity is known.  Any such model restricts to
a hyperlinear model of `SL_r(F_q[t,1/t]) *_(SL_r(F_q[t])) SL_r(F_q[t,1/t])`.
