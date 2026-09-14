---
rg: 2
id: reducer-by-factor-unfolding
kind: route
title: Reduce locality by replacing each amplified tensor clause with the average of its factors
target: locality-reduction-with-amplifier-independent-loss
requires: []
artifacts:
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
---

**Dead.** Invalidated by `unfolding-tensor-clauses-returns-the-original-gap`.

The tempting argument. An amplified clause `I - tensor_j(I-Pi_(f(j)))` is
violated exactly when some factor is violated. So spread its penalty over its
`2t` factors, each `k`-local. The result keeps completeness, is layered, and
has constant locality.

Why it fails. The spread Hamiltonian is the average of `2t` copies of the input,
by walk stationarity. Its ground energy is exactly `lambda_min(H)`, so the
amplification is undone, and (RED1) holds only with `c<=sqrt(log t/t)/eta`.
A reducer must use the tensor structure, for instance by checking the AND
coherently while keeping constant locality and a `t`-independent loss. That is
the open content of the target.
