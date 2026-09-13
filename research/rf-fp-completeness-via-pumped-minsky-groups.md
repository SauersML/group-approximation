---
rg: 2
id: rf-fp-completeness-via-pumped-minsky-groups
kind: route
title: INF reduces to residual finiteness through pumped clocked Minsky machine groups
target: residual-finiteness-of-finite-presentations-is-pi2-complete
requires:
  - clocked-search-machine-halts-universally-exactly-on-inf
  - pumped-halting-clocked-minsky-group-is-residually-finite
  - pumped-divergent-minsky-word-lies-in-profinite-kernel
  - residual-finiteness-of-enumerated-presentations-is-pi3-complete
artifacts:
  - research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md
  - research/artifacts/rf-fp-pumped-minsky-part2-2026-09-12.md
  - research/artifacts/rf-fp-pumped-minsky-part3-2026-09-12.md
---

## Why sufficient

`e |-> G(P(M_e))` is a computable map to finite presentation codes: the
switch machine, the pumping construction, then the KMS relations G1--G8.

- On `INF`, `M_e` is universally halting
  ([[clocked-search-machine-halts-universally-exactly-on-inf]]), so the group
  is residually finite
  ([[pumped-halting-clocked-minsky-group-is-residually-finite]]).
- On `FIN`, `M_e` has a divergent configuration, so the group is not
  residually finite
  ([[pumped-divergent-minsky-word-lies-in-profinite-kernel]]).

Hence `INF <=_m RF_fp` and `FIN <=_m NONRF_fp`.  `INF` is `Pi^0_2`-complete.
`RF_fp in Pi^0_2` is the finite-presentation clause of
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]].  Hardness
and membership give completeness, and the complement is `Sigma^0_2`-complete.
