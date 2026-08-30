---
rg: 2
id: stw01-stable-ideal-extension-proof
kind: route
title: Apply stable-algebra invisibility and the quotient transfer principle
target: stw01-stable-ideal-extensions-force-qt-linearity
requires:
  - stw01-stable-algebras-are-bounded-quasitrace-invisible
  - stw01-qt-invisible-ideal-extension-principle
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

By `stw01-stable-algebras-are-bounded-quasitrace-invisible`, the stable ideal
`I` carries no nonzero bounded `2`-quasitrace.  The hypothesis says that every
bounded `2`-quasitrace on `Q=A/I` is a trace.  Applying
`stw01-qt-invisible-ideal-extension-principle` proves that every bounded
`2`-quasitrace on `A` is a trace.

The orthogonal multiplier-isometry argument formerly duplicated here is now
contained entirely in
`stw01-orthogonal-multiplier-isometries-kill-bounded-quasitraces`.
