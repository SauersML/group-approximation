---
rg: 2
id: anti-central-state-obstruction-equals-stable-finiteness
kind: claim
title: A state obstruction to the ternary anti-central corner exists exactly when no multiple of the unit class is nonpositive
distinct_from:
  ternary-anti-central-unit-class-is-nonpositive: that is the open stable condition k[eps_-] <= 0, which suffices for a counterexample; this is the established equivalence between the absence of that condition and the existence of a state, together with the fact that the corner equation forces the condition.
  finite-precision-lifted-trace-obstruction: that constructs additive p-adic trace invariants, which cannot see positivity; this identifies positivity-carrying states as the only possible obstruction and characterizes when they exist.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

Let `R = L_(F_3)(1,2)`, `G = R^x`, `S_- = eps_- F_3[G]`, `u = [eps_-]` in the preordered group
`K_0(S_-)`, and `e_-` the anti-central swap idempotent of `ternary-anti-invariant-swap-corner-is-full`.

1. If `c e_- b = eps_-` is solvable in `S_-`, then `u <= 0`. So `S_-` has no state normalized at
   `eps_-`, and no Sylvester matrix rank function with `N(eps_-) = 1`. It is also properly infinite.
2. A state on `(K_0(S_-), u)` exists iff `k u` is not `<= 0` for every `k >= 1`.
3. If `k u <= 0` for some `k >= 1`, then some `M_r(F_3[G])` is not directly finite, and `G` is not
   surjunctive.

So a positivity-type obstruction to the corner equation exists exactly when `S_-` is stably finite
in the sense of part 2, and the failure of that condition is itself a counterexample. Every additive
group-valued invariant, including traces mod 3 and the lifted traces `t_(3,k)`, cannot refute the
equation, because `[eps_-] = 2[e_-]`.

Proof: Theorem A and Theorem B(i) of the artifact. The state criterion (Goodearl–Handelman form) is
proved there by a Hahn–Banach argument, so no import is needed.
