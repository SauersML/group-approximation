---
rg: 2
id: opnorm-packet-collision-kills-phase
kind: claim
title: One operator-norm packet collision forces the twisted phase close to the identity
distinct_from:
  bounded-area-high-chromatic-conjugacy-collapse: that is a normalized-HS Carmichael relation estimate using bounded relator area; this is a four-unitary operator-norm estimate with no trace or density.
  opnorm-coordinatewise-capacity-diagonal: that is the later abstract dimension diagonal; this supplies the local collision detector used to instantiate its finite-capacity premise.
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
  - GroupApproximation/Sofic/NoRenormalizationCapacity.lean
---

Let `A,B_v,B_w,Z` be unitary matrices. If

```text
||A B_v-Z B_v A||_op <= epsilon,
||A B_w-B_w A||_op <= epsilon,
||B_v-B_w||_op <= delta,
```

then

```text
||Z-I||_op <= 2 delta+2 epsilon.
```

The estimate is independent of matrix dimension and support rank. It is
machine-checked as
`NoRenormalizationCapacity.collision_kills_phase`.
