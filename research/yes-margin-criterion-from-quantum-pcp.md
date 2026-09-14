---
rg: 2
id: yes-margin-criterion-from-quantum-pcp
kind: route
title: A quantum PCP reduction, shifted, satisfies the YES margin together with the whole anchored criterion
target: amplifier-preserves-yes-energy-below-the-floor
requires: [quantum-pcp-constant-gap-local-hamiltonian, anchored-criterion-components-are-shift-satisfiable]
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
---

## Why sufficient

Let `R*` witness `quantum-pcp-constant-gap-local-hamiltonian`. By the converse
half of `anchored-criterion-components-are-shift-satisfiable`, the shifted
reduction `R*_epsilon` has combinatorial gap one, a uniform rounder constant
`C=1/((1-epsilon)b*+epsilon)`, and YES energy below `beta/C` by
`(1-epsilon)(b*-a*)=Omega(1)`. All three hold for the one reduction the
definite description in (YES1) refers to.

## Why the cycle is deliberate

This route and `qpcp-from-anchored-amplifier` form the cycle
`quantum-pcp-constant-gap-local-hamiltonian -> amplifier-preserves-yes-energy-below-the-floor -> quantum-pcp-constant-gap-local-hamiltonian`.
Both implications are true, so the two claims are equivalent. Recording both
directions makes it visible in the graph that the anchored route reduces the
root to a claim equivalent to the root. A least fixpoint never fires a cycle,
so neither claim establishes itself. Do not delete either route to silence
the cycle warning.
