---
rg: 2
id: atlas-l44-bitpacked-packet-collision-screen-proof
kind: route
title: Bit-pack every common H6 frame and replay H18 plus collision
target: atlas-l44-subfield-packet-collision-exclusion
requires:
  - atlas-l44-h6-has-thirty-frobenius-frames
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_a4_l44_bitpacked_screen.py
  - experiments/atlas-a4-l44-bitpacked-screen.json
---

Represent `Mat_4(F4)` as a 32-dimensional `F2` vector space.  Each common
conjugator equation `Xg=gY` is a bit-packed linear system.  Gaussian
elimination gives an explicit kernel basis, and enumerating its nonzero span
tests invertibility exactly.  For the first five pairs, independent Sage
matrix conjugation assertions certify both the equation orientation and the
common kernel dimension `10`.

An exact GAP class scan produces the `336` H6 fan images and all `1262`
ordered rectangle pairs.  All `1262` lift.  For each lift, multiplying one
chosen conjugator by the exact projective H6 centralizer of order `180`
enumerates its whole common-frame fiber once.  Literal F4 multiplication then
tests both directed H18 rectangle systems and leaves `2754` packet survivors.
Their frame split is `30+2724`, and literal word evaluation gives `(L44S1)`
and zero collision survivors.

The second replay applies the noninner automorphism `(g^-1)^T` to every
second-chart packet label and second-chart collision/q14 letter.  It produces
the same packet and collision counts.  Thus both relative marking parities
are exhausted.  Assertions pin every count and histogram in the artifact;
there is no sampling or floating-point computation.
