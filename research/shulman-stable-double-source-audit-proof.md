---
rg: 2
id: shulman-stable-double-source-audit-proof
kind: route
title: Read the current arXiv v2 theorem statements and separate the homotopy trace result
target: shulman-symmetric-double-has-no-stable-trace-upgrade
requires: []
artifacts:
  - research/artifacts/shulman-2603-13564-verified.md
  - notes/FALSE_SHULMAN_TRACE_AUDIT.md
---

The arXiv API identifies 2603.13564v2 as the current version.  Its abstract,
introduction, full text, and theorem list were checked against the PDF.
Theorem 10 is exactly `(SHT1)`; searches of the full text find no
Hilbert--Schmidt-stability or hyperlinear-trace theorem.  Theorem 20 has the
compatible norm-corona statement already transcribed in the verification
artifact.

The superficially similar trace statement was checked in the separate paper
arXiv:2508.00125.  Its Corollary 35 has the homotopy-domination hypothesis,
and the variance calculation for the fold maps is recorded in
`notes/FALSE_SHULMAN_TRACE_AUDIT.md`.  Thus it cannot be substituted for a
trace-preserving symmetric-double theorem.

