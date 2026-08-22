---
rg: 2
id: canonical-trace-square-blindness-proof
kind: route
title: Compute the adjoint character and the half-block flip
target: canonical-trace-square-is-blind-to-iwahori-overlap
requires: []
artifacts:
  - research/artifacts/canonical-iwahori-one-overlap-audit-2026-08-21.md
---

Under vectorization, `Ad_U` is `U tensor bar(U)`.  Its normalized trace is
`tr_d(U) overline(tr_d(U))`, proving `(CTS1)`.  The matrices in `(CTS2)`
have the displayed traces, the flip exchanges the two diagonal blocks, and
direct multiplication gives `(CTS3)`.  Formula `(IOS2)` then gives
`phi_P(U)=(0-1/4)/(1/4)=-1`.
