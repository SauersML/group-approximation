---
rg: 2
id: ternary-counterexample-from-rank-kill-and-state-realization
kind: route
title: No Sylvester rank function sees minus one, states would be rank functions, so no state exists and the unit class is nonpositive
target: ternary-anti-central-unit-class-is-nonpositive
requires: [sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one, ternary-anti-central-states-give-sylvester-rank-functions, anti-central-state-obstruction-equals-stable-finiteness]
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

Artifact Section 4.4. This is the sharpest form of Plan 1, with no matrix approximation step.
1. By the first requirement, `S_-` has no Sylvester matrix rank function with `N(eps_-) = 1`.
2. By the second requirement, taken in contrapositive, `(K_0(S_-), [eps_-])` has no state.
3. By part 2 of the third requirement, `k[eps_-] <= 0` for some `k >= 1`. That is the target, which refutes
   Gottschalk on `L_(F_3)(1,2)^x` through `nonpositive-unit-class-refutes-ternary-surjunctivity`.

The first requirement is necessary for the target. So this route loses nothing: the target holds iff the
first requirement holds, given the second.
