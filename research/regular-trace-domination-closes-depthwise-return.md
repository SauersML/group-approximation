---
rg: 2
id: regular-trace-domination-closes-depthwise-return
kind: route
title: Convert regular trace domination into every fixed-depth matrix estimate
target: fanizza-depthwise-fixed-mark-return
requires:
  - fanizza-regular-trace-heat-domination-compiler
  - canonical-moments-linearize-fixed-depth-fanizza-return
---

Clause `(RHC1)` is HALT completeness.  For fixed `t`, apply the canonical
moment linearization theorem to `(RHC2)` with `P=P_m`, `A=A_(m,t)` and
`b=0`.  Its finite relator prefix, finite canonical window and finite
constant are exactly `(DFR1)`.  No uniformity in `t` is used.

