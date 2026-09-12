---
rg: 2
id: ternary-counterexample-from-rank-triviality-and-state-upgrade
kind: route
title: No characteristic-three rank model plus the state upgrade leaves no state, so the unit class is nonpositive
target: ternary-anti-central-unit-class-is-nonpositive
requires: [leavitt-el3-rank-models-over-finite-fields-are-trivial, leavitt-gl-equals-el-and-perfect-unit-group, ternary-anti-central-states-force-nontrivial-rank-models, anti-central-state-obstruction-equals-stable-finiteness]
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
  - research/artifacts/upg-chain-audit-2026-09-12.md
---

Artifact Section 2.
1. By the first requirement, `G_3` has no nontrivial characteristic-three rank model. Any other proof of
   the "No" branch of `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model` serves as well.
   The first requirement is about homomorphisms of `EL_3(R)`. To pass from those to all of `G_3`, use
   `G_3 ~= GL_3(R) = EL_3(R)`: the three-leaf prefix code, plus the second requirement.
   A model over matrix algebras with varying fields of characteristic three embeds rank-preservingly
   into one over a single algebraically closed field, so the fixed-field form of the first requirement is
   enough (audit artifact, Section 2.1).
2. By the contrapositive of the second requirement, `(K_0(S_-), [eps_-])` has no state.
3. By part 2 of the third requirement, `k[eps_-] <= 0` for some `k >= 1`. That is the target, which
   refutes Gottschalk through `nonpositive-unit-class-refutes-ternary-surjunctivity`.
