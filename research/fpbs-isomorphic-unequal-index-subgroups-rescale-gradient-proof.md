---
rg: 2
id: fpbs-isomorphic-unequal-index-subgroups-rescale-gradient-proof
kind: route
title: Induce the boundary of a Farber chain through each subgroup, transport it by the isomorphism, and read costs off Abert-Nikolov
target: fpbs-isomorphic-unequal-index-subgroups-rescale-gradient
requires:
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

The written proof is Section 1 of the linked note.

- **Lemma 1.1.** Prepending `G` to a Farber chain of an index-`k` subgroup
  `H` gives boundary `{1..k} x dT_H` with product measure. The stabilizers
  are `t_j Stab_H(x) t_j^{-1}`, so the chain is Farber, and its gradient is
  divided by `k`, since `d` is unchanged and indices are multiplied by `k`.
- **Lemma 1.2.** An isomorphism carries boundaries, measures, stabilizers and
  gradients across.
- **Costs.** Abert--Nikolov Theorem 1, whose verbatim statement allows
  non-normal Farber chains, converts the gradients into the costs of the
  boundary relations.

This is a written deduction, not a formal verification.
