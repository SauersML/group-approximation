---
rg: 2
id: fpbs-relative-cycle-retraction-rounding-proof
kind: route
title: Identify the deleted-edge module with the retraction kernel and bound its orthogonal complement
target: fpbs-relative-cycle-retraction-rounding
requires:
  - fpbs-relative-cycle-operator-descent
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Section 7. For the deleted-edge set D, the bounded map w->w-Rw is
an equivariant isomorphism from C_1(D) onto ker R, with inverse the
deleted-edge coordinate projection. Thus the kernel projection P_W
has trace c(H)-c(J). Since v-Rv lies in W, the nearest-point property
gives ||(I-P_W)v||<=||Rv||. Apply this to K^(1/2), take traces, and
use Tr(P_W K)<=Tr(P_W). This proves the general inequality; the
required operator-descent identity gives its relative version.
The artifact checks path length and congestion for bridge collapse,
recovers the earlier block estimate, and verifies exact cancellation
in the known finite-fiber example without a universal extrapolation.
