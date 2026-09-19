---
rg: 2
id: agent-first-hit-named-corner-holonomy-seam-proof
kind: route
title: Place the exact corner theorem after the metric reflection gate and discard the redundant phase cell
target: agent-first-hit-named-corner-holonomy-seam
requires:
  - agent-free-compressor-minimal-nonretractive-corner
  - finite-group-multiplicity-mismatch-pays-hs-energy
  - agent-first-hit-cross-holonomy-does-not-reflect-named-corner
---

The exact coefficient calculation proves the last implication in `(NCH2)`.
The split model of
`agent-first-hit-cross-holonomy-does-not-reflect-named-corner` proves that a
finite phase cell cannot imply either preceding implication.  Therefore the
only useful positive route retains the existing payload-to-root and fixed-row
reflection gates, after which finite-group multiplicity mismatch pays the
rank jump directly.
