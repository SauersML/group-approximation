---
rg: 2
id: thompson-v-modular-group-algebras-are-stably-finite
kind: claim
title: Every group algebra of Thompson's V over a field of positive characteristic is stably finite
refuted_by:
  - thompson-v-modular-group-algebra-not-directly-finite
distinct_from:
  thompson-v-modular-group-algebra-not-directly-finite: that asks for a one-sided unit in some F_p[V], which would refute this.
  linear-sofic-group-algebra-is-stably-finite: that is the general passage from linear soficity to stable finiteness; this is the conclusion for the one group V, whose linear soficity is open.
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**OPEN.** For every field `k` of positive characteristic and every `n >= 1`, `B A = I_n` in
`M_n(k[V])` implies `A B = I_n`.

## Attempts

- **From soficity.** `thompson-v-stable-finiteness-from-soficity`. Soficity of `V` is open.
- **From linear soficity.** `linear-sofic-group-algebra-is-stably-finite` needs `V` to be
  `k`-linear sofic, which is open.
- **Representation-theoretic proofs.** Unavailable. Every finite-dimensional representation of
  `V` is trivial, and the identity-coefficient trace carries no positivity in positive
  characteristic (Section 4 of the artifact).
