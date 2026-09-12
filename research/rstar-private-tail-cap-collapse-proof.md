---
rg: 2
id: rstar-private-tail-cap-collapse-proof
kind: route
title: Determinize each private tail over the retained binary spectrum
target: rstar-private-tail-fiberwise-cap-collapse
requires:
  - isolated-rstar-context-determinizes-to-a-fano-cap
---

Apply `isolated-rstar-context-determinizes-to-a-fano-cap` independently at
each occurrence.  Its replacement changes only the three tail observables
and keeps the retained first observable fixed.  By hypothesis those tails
occur nowhere else, so the replacements do not conflict and every other
context relation is unchanged.  All new observables lie in the original CE
algebra; a trace-preserving embedding into `R^omega` restricts to their
generated von Neumann subalgebra.
