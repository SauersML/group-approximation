---
rg: 2
id: rank-condition-rings-carry-sylvester-rank-functions
kind: claim
title: Every ring with the rank condition carries a Sylvester matrix rank function
distinct_from:
  sylvester-rank-functions-iff-no-triangular-certificate: that is the established certificate criterion for existence; this asks whether the rank condition, the minors-only criterion, already implies it.
  twisted-leavitt-corner-fullness-equals-absence-of-k0-states: that shows K_0 states exist iff the rank condition holds; this asks whether a K_0 state upgrades to a Sylvester rank function on every ring.
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

**OPEN.** Let `A` be a unital ring such that no epimorphism `A^q -> A^(q+1)` exists, equivalently
`(K_0(A), [A])` admits a state. Then `A` carries a Sylvester matrix rank function.

By `sylvester-rank-functions-iff-no-triangular-certificate`, this says: whenever
`I_(q+1)` lies below `I_q` through minors and triangular moves, it already does through minors alone.
It is step (U1) of `ternary-anti-central-states-force-nontrivial-rank-models`, for arbitrary rings. A
counterexample is the calibration ring that kills (U1) in general. It would not by itself kill (U1) for
`S_-`, which is `anti-central-triangular-certificates-flatten-to-minors`.

## Attempts

- 2026-09-12 `w4-upg-kill` (artifact Sections 1–4). The kill test found neither a counterexample nor a
  proof.
  - **Holds on its own:** chains whose carried identity minors split along the blocks, and idempotent
    triangular steps (`split-identity-minors-survive-triangular-moves`).
  - **Holds from the literature (not re-read locally):**
    - regular rings, where Goodearl's pseudo-rank functions correspond to `K_0` states;
    - any ring with a unital map into a regular ring that has the rank condition;
    - Leavitt path algebras of finite graphs (Ara–Brustenga).
  - **Shape of a counterexample.** A non-idempotent triangular step at a carried minor that mixes the two
    diagonal blocks.
  - **Not checked.** Whether the literature settles this: Malcolmson; Schofield, *Representations of Rings
    over Skew Fields*, Chapter 7; Jaikin-Zapirain's survey. No local copies.
