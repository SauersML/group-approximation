---
rg: 2
id: one-sided-conjugator-sofic-proof
kind: route
title: Rewrite the cyclic kernel and apply triangular amalgamation
target: one-sided-conjugator-one-relator-groups-are-sofic
requires: [triangular-conjugate-bs-chains-are-sofic]
artifacts:
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
  - experiments/one_relator_cyclic_peeling_check.py
  - research/artifacts/one-relator-cyclic-peeling-replay-2026-09-07.json
---

The character `a->0, b->1` is well-defined and surjective. Its kernel has
generators `a_i=b^(-i)ab^i` and relators

    c_i^(-1) a_i^l c_i = a_i^k,
    c_i = V_i^(-1) a_(i+d) V_i,

where `V_i` is obtained by adding `i` to each index of `V`. An explicit
semidirect-product presentation in the artifact verifies this kernel
identification, not just a surjection onto it. Every index in `V_i`, and
`i+d`, is greater than `i`, so the prerequisite applies. The quotient of
the original group by this sofic kernel is `Z`, hence amenable. The
sofic-kernel/amenable-quotient theorem completes the proof.
