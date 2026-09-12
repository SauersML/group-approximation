---
rg: 2
id: kt-q2-double-reduced-algebra-has-unique-trace
kind: claim
title: The q=2 Kun--Thom double has unique reduced C-star trace
distinct_from:
  kt-double-reduced-cstar-is-mf: that asks for a norm-corona embedding of the reduced algebra; this establishes only that any such embedding would automatically select the canonical trace.
  reduced-amalgam-canonical-trace-is-mf: that asks for MF microstates carrying the canonical trace on the full group C-star algebra; this is uniqueness of traces on the reduced algebra and supplies no microstates.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

For the explicit `q=2` Kun--Thom double `D=G *_Gamma G`, the reduced group
C-star algebra `C*_r(D)` has exactly one tracial state, its canonical regular
trace.

The group-theoretic input is the established
`kt-q2-double-has-trivial-amenable-radical`.  The
Breuillard--Kalantar--Kennedy--Ozawa unique-trace theorem, already cited in
the canonical artifact, identifies triviality of the amenable radical with
the unique-trace property of the reduced group C-star algebra.

This removes trace selection only *after* an approximation factors through
`C*_r(D)`.  It does not make the reduced algebra MF and does not repair the
profinite Shulman model, which is nontempered already on a vertex.
