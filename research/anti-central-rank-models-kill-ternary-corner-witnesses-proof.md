---
rg: 2
id: anti-central-rank-models-kill-ternary-corner-witnesses-proof
kind: route
title: Compress the model to the minus-one eigen-corner, read the rank as a state, and use the dihedral halving
target: anti-central-rank-models-kill-ternary-corner-witnesses
requires: []
artifacts:
  - research/artifacts/ternary-corner-state-sources-2026-09-12.md
---

Sections 1–2 of the artifact.

- `f = 2(1 − σ(z))` is an idempotent commuting with `σ(Γ)`. It is nonzero because `σ(z) != 1`.
- `x -> σ(x) f` gives a unital ring map `S_Γ -> fMf`, because `[z]` goes to `−f` and so `eps_-` goes
  to `f`.
- The normalized rank `ρ(·)/ρ(f)` on idempotent matrices is additive and invariant under algebraic
  equivalence, so it is a state normalized at `eps_-`.
- In `G`, `d w d^-1 = z w` (Lemma 1.1). So `[d] e_- [d]^-1 = eps_- − e_-`, and the state takes the value
  `1/2` on `e_-`.
- A solution of `c e_- b = eps_-` makes `eps_-` equivalent to the subidempotent `e_- b c e_-` of `e_-`,
  which forces `1 <= 1/2`.

The injectivity remark in the global form cites `leavitt-gl-equals-el-and-perfect-unit-group` and
`odd-leavitt-unit-groups-mod-scalars-are-fp-simple` in prose only. The theorem needs no prerequisite.
