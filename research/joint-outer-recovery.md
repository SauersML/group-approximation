---
rg: 2
id: joint-outer-recovery
kind: route
title: One comb compressor jointly recovers both outer transitions
artifacts:
  - notes/TRUE_ONE_COMPRESSOR_JOINTLY_RECOVERS_BOTH_OUTER_TRANSITIONS.md
target: outer-pvm-synchronization
requires: [finite-window-decoder]
---

In rank five, with the complete four-root chain in the rank-four core, the
same comb compressor implements `α(a) = s₀ a t₀` on both commuting outer
root groups. Exactify their product group and apply covariance once to
`α × α`: marginal RMS defects `e_L, e_R` give a joint defect `≤ e_L + e_R`,
hence one joint extension-character PVM with total rounding error below
`9(e_L + e_R)²`, of which both outer transition measurements are exact
coarsenings. No PVM-synchronization or marginal-matching gate remains: the
synchronization goal outer-pvm-synchronization reduces to the finite-window endomorphism
decoder finite-window-decoder.
