---
rg: 2
id: stw99-lv-via-dual-trace-scaling-spectrum
kind: route
title: Separate the quasifree flows by the dual trace-scaling exponent
target: stw99-problem-lv-quasifree-flows-o2
requires:
  - stw99-lv-dual-trace-scaling-spectrum-cocycle-invariant
artifacts:
  - research/artifacts/stw99-late-band-audit-2026-08-31.md
---

For irrational `lambda>0`, Kishimoto--Kumjian prove that
`O_2 rtimes_(alpha^(lambda)) R` is simple and stably projectionless with a
unique densely defined lower semicontinuous tracial ray.  Quasifree KMS
theory supplies a state exactly at the unique positive inverse temperature
`beta(lambda)` satisfying

```text
exp(-beta)+exp(-lambda beta)=1.
```

The equation is also forced directly by the KMS identity applied to the two
Cuntz isometries and by `s_1s_1^*+s_2s_2^*=1`.  The dual trace associated to
that KMS state is scaled by the dual flow with character
`s |-> exp(-beta(lambda)s)`.  Uniqueness of the tracial ray identifies this
with the character in
`stw99-lv-dual-trace-scaling-spectrum-cocycle-invariant`.

At fixed positive `beta`, the left side of the displayed equation is strictly
decreasing in `lambda`.  Consequently its unique root `beta(lambda)` is
strictly decreasing in `lambda`.  Cocycle conjugacy therefore forces equal
parameters.  Equal parameters give identical flows, completing the
classification.

