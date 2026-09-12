---
rg: 2
id: low-degree-kaplansky-failure-via-unipotent-surjectivity
kind: route
title: Split a low-degree strict pair by its linear parts and discard the unipotent branch
target: low-degree-strict-automata-force-matrix-kaplansky-failure
requires:
  - low-degree-strict-pairs-have-one-sided-linear-parts
  - unipotent-automata-over-finite-fields-are-surjective
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Let `tau` be strict with left inverse `sigma` and `deg sigma * deg tau < q`. After
normalization, the first prerequisite gives linear parts with `C A = I_m`.

- If `A C != I_m`, then `M_m(F_q[G])` is not directly finite, and restriction of scalars gives
  a failure over `F_p` at matrix size `mk`.
- If `A C = I_m`, then `tau_C tau` is a strict unipotent automaton satisfying the same degree
  bound, which the second prerequisite forbids.

So the first case occurs, and the target holds.
