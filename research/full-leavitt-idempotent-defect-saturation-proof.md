---
rg: 2
id: full-leavitt-idempotent-defect-saturation-proof
kind: route
title: Multiply through the full idempotent and permute root positions
target: full-leavitt-idempotent-defect-saturation
requires: []
artifacts:
  - research/artifacts/hilbert-hotel-st20-full-mf-radical-2026-08-21.md
---

The coefficient after the two commutators is
`a*t1*q*s1=a`.  Thus the normal closure contains `x_42(a)` for every
coefficient.  Elementary Weyl words move `(4,2)` to every ordered pair of
distinct indices, and root subgroups generate the Steinberg group.  The same
conclusion is machine-checked as
`BinaryLeavittSteinberg.normalClosure_root_eq_top`.
