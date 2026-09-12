---
rg: 2
id: nested-defects-in-kazhdan-groups-proof
kind: route
title: Conjugate the nested element back into the Kazhdan group and apply the sofic defect criterion there
target: nested-rigid-defects-live-in-nonsofic-kazhdan-groups
requires:
  - sofic-groups-kill-rigid-compression-defects
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Derivation (artifact Proposition 6.1 and Corollary 6.2).

1. `z = t^-1 w t`, with `t` and `w` in `G`.
2. `z` centralizes `Gamma`, but its conjugate `w` does not.
3. The pair `Gamma <= G <= G` carries a nontrivial rigid defect. That is impossible in
   a sofic group by `sofic-groups-kill-rigid-compression-defects`; with ambient group
   `G`, this is Kun--Thom Theorem B.
4. `w in Gamma` fails to commute with some element of `Gamma` exactly when `w` lies
   outside `Z(Gamma)`, and `z` ranges over `C_G(Gamma) ∩ t^-1 Gamma t`.
5. An automaton whose memory lies in `G` runs independently on the cosets of `G`. So a
   strict pair over `G` is one over `H`, and the case `H = G` implies the general
   statement.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 17 of the
verification artifact).
