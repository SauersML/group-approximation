---
rg: 2
id: ternary-counterexample-from-rank-triviality-and-state-upgrade
kind: route
title: No characteristic-three rank model plus the state upgrade leaves no state, so the unit class is nonpositive
target: ternary-anti-central-unit-class-is-nonpositive
requires: [leavitt-el3-rank-models-over-finite-fields-are-trivial, ternary-anti-central-states-force-nontrivial-rank-models, anti-central-state-obstruction-equals-stable-finiteness]
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

Artifact Section 2.
1. By the first requirement, `G_3` has no nontrivial characteristic-three rank model. Any other proof of
   the "No" branch of `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model` serves as well.
2. By the contrapositive of the second requirement, `(K_0(S_-), [eps_-])` has no state.
3. By part 2 of the third requirement, `k[eps_-] <= 0` for some `k >= 1`. That is the target, which
   refutes Gottschalk through `nonpositive-unit-class-refutes-ternary-surjunctivity`.
