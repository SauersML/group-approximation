---
rg: 2
id: stw91-exact-cstar-simple-groups-have-unique-quasitrace-proof
kind: route
title: Combine Haagerup's quasitrace theorem with the unique-trace property
target: stw91-exact-cstar-simple-groups-have-unique-quasitrace
requires: []
artifacts:
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

Exactness of `G` means that `C*_r(G)` is exact.  Haagerup's theorem says that
every bounded 2-quasitrace on a unital exact C*-algebra is a trace.  On the
other hand, every C*-simple discrete group has the unique-trace property: its
canonical trace is the only tracial state on its reduced C*-algebra.  Hence
every normalized 2-quasitrace on `C*_r(G)` is the canonical trace.

The final two sentences of the claim are contrapositives and a separation of
Robert's necessary conditions; they do not assert that stable rank one and
strict comparison suffice for selflessness.

**Trust boundary.**  This route imports Haagerup's theorem that quasitraces
on exact C*-algebras are traces and the Breuillard--Kalantar--Kennedy--Ozawa
implication from C*-simplicity to the unique-trace property.  No converse to
Robert's regularity theorem is used.
