---
rg: 2
id: anti-central-state-lifted-trace-extension-proof
kind: route
title: The additive lifted trace makes the finite-subgroup trace well defined, and a one-step Zorn extension turns relative positivity into a state
target: anti-central-state-exists-iff-lifted-trace-relatively-positive
requires:
  - lifted-trace-detects-finite-subgroup-projectives
  - anti-central-k0-states-equal-lifted-trace-on-signed-thompson
  - twisted-leavitt-corner-fullness-equals-absence-of-k0-states
artifacts:
  - research/artifacts/lifted-trace-state-extension-2026-09-12.md
---

Sections 1–2 of the artifact.
- **Part 1:** `t_3` is additive on `K_0(F_3[G])` and equals `dim/|K|` on finite-subgroup projectives. Rational numbers
  inject into `Z_3` (Corollary 1.2).
- **Part 2:** idempotent lifts over `c_0(G, Z_3)` (Proposition 1.1).
  - *Halving.* `F_*([p]) = [e_- delta_*(p)]`. `e_-` lifts to `(1-z)(1+w)/4`, which commutes with `delta_*` of a lift.
  - *Identity coefficient.* `w` and `zw` are not in `delta(G)`, and an anti-central lift has `b_(zg) = -b_g`. So the
    identity coefficient halves.
  - *Transpose.* `alpha` is a group automorphism fixing `z`.
- **Part 3:** Lemma 2.1, the extension of relative states on a preordered group with an order unit. It is proved by
  Zorn's lemma, with the one-step extension value chosen between the sup and inf of the rational bounds.
- **Part 4:** necessity from the forced-states theorem; sufficiency from part 3 with `L = H_fin(H)`.
- **Part 5:** part 4 together with Theorem E. The witness class comes from census Theorem A(a).
