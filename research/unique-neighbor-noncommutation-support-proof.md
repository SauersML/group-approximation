---
rg: 2
id: unique-neighbor-noncommutation-support-proof
kind: route
title: Apply the stopping-set argument to every commutator row
target: unique-neighbor-ldpc-checks-force-dense-noncommutation
requires: []
---

Fix `j` and mark coordinate `i` exactly when `[Q_i,Q_j]` is nonzero.  The
parity identity on a check having a unique marked coordinate rewrites that
coordinate reflection as a product of unmarked reflections, all of which
commute with `Q_j`; this is impossible.  Thus the marked set is a stopping
set and has size at least `sigma L` when nonempty.  Symmetry of
noncommutation supplies at least `sigma L` nonempty rows, each of size at
least `sigma L`, giving the claimed quadratic support bound.
