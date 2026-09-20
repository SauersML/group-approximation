---
rg: 2
id: wave2-ghb7-scalar-phase-camouflage-proof
kind: route
title: Enlarge one scalar power defect while preserving the adjoint tuple, centrality errors and flexible-rounding obstruction
target: wave2-ghb7-raw-supercentrality-does-not-reduce-stability
requires: []
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-matching-2026-09-20.md
---

Section 4 gives the full conditional transformation. Given an alleged
fixed-gap nonroundable sequence with total doubled defect epsilon_n>0,
put t_n=epsilon_n^(1/(k+1)) and multiply both a entries by exp(i t_n).
All commutator relators and copy mismatches are unchanged; the a^7
relator is multiplied by exp(7i t_n). Hence the new maximum plus defect
is asymptotic to 7t_n, while centrality is unchanged and <=2epsilon_n.
Their ratio kappa/delta^k tends to zero. Conjugation operators are
unchanged, so the gap remains fixed. Flexible rounding cost changes
by at most the vanishing maximum generator 2-distance, preserving a
positive lower bound. The theorem is conditional and claims no
existence of an unstable GHB7 tuple.
