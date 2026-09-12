---
rg: 2
id: nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple
kind: claim
title: A left-invertible element of a rank-ultraproduct corner is invertible, so no nonzero corner holds a Cohn triple
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that forbids a unital ring homomorphism from L_(F_2)(1,2) into a rank ultraproduct; this is an operator statement in a corner with three relations and no algebra homomorphism, over every field and characteristic, and it implies that claim for every L_K(1,2).
  rank-four-isometry-relations-give-corner-cuntz-family: that is the open construction of a corner Leavitt family from a nonzero two-root defect; this is the endpoint it aims at, shown to need only T_0 S_0 = e, T_0 S_1 = 0, T_1 S_1 = e and to be impossible outright for e != 0.
  binary-leavitt-algebra-not-directly-finite: that is the ring identity t_0 s_0 = 1 != s_0 t_0 in the Leavitt algebra; this is direct finiteness of every corner of every rank ultraproduct.
artifacts:
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

**ESTABLISHED** (proof route `nonzero-rank-corner-cohn-toeplitz-triple-proof`).

Let `k` be any field and `M = prod_omega M_(n_i)(k) / d_omega` a rank ultraproduct. Let `e` be an
idempotent of `M`, and let `S_0, T_0` lie in `eMe` with `T_0 S_0 = e`.
1. `S_0 T_0 = e`.
2. Every `S` in `eM` with `T_0 S = 0` is zero.
3. If `S_1` is in `eM`, `T_1` is in `M`, `T_0 S_1 = 0` and `T_1 S_1 = e`, then `e = 0`.

In particular, no nonzero corner `eMe` contains an order-two Leavitt family, or even a two-pair Cohn
family `T_i S_j = delta_ij e`. Neither the completeness relation `S_0 T_0 + S_1 T_1 = e` nor the second
off-diagonal relation is needed.

## Why it matters for family R4

- **Plan 1's endpoint needs three relations.** `rank-four-isometry-relations-give-corner-cuntz-family`
  only has to produce, from a nonzero two-root defect, an idempotent `e != 0` with `S_0, T_0` in `eMe`,
  `T_0 S_0 = e`, and a nonzero `S_1` in `eM` with `T_0 S_1 = 0`. Check (ii) and half of check (i) drop out.
- **That configuration can never exist**, so the plan claim is, model by model, equivalent to `D = 0`.
  It is a proof strategy by contradiction for the gate, not a reduction of the gate to a weaker open
  statement.
- **The `D = 0` branch of `leavitt-el3-triviality-via-rank-four-cuntz-family`** needs no unital rank
  model of `L_K(1,2)` for any finite `K`. `leavitt-algebra-has-no-unital-rank-model` is stated for
  `F_2` only; this claim covers every `K`.

## Attempts

Established, not open. The proof is the identity `rk(1 - ab) = rk(1 - ba)`, applied to
`a = S_0 + (1 - e)` and `b = T_0 + (1 - e)`. Artifact Section 1.
