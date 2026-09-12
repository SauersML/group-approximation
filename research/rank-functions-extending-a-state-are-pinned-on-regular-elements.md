---
rg: 2
id: rank-functions-extending-a-state-are-pinned-on-regular-elements
kind: claim
title: A rank function extending a K_0 state is determined on von Neumann regular elements and undetermined on nilpotents
distinct_from:
  anti-central-k0-states-equal-lifted-trace-on-signed-thompson: that computes what every state is on finite subgroups of the signed Thompson group; this shows what such a state does and does not force on a rank function extending it.
  sylvester-rank-function-quotients-are-weakly-finite: that is about the null ideal of a rank function; this sandwiches rank functions between two ranks computed from a state.
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

**ESTABLISHED** (artifact Proposition B). Let `s` be a state on `(K_0(A), [A])`. Define:
- `rho_s(X)`: the infimum of `s([P])` over f.g. projectives `P` that `X` factors through;
- `rho^s(X)`: the supremum of `s([f])` over idempotent matrices `f = L X R`.

Then:
1. `rho^s <= rho_s`.
2. Every Sylvester matrix rank function `N` agreeing with `s` on idempotent matrices satisfies
   `rho^s <= N <= rho_s`.
3. If `X = XYX`, then `rho^s(X) = rho_s(X) = s([XY])`. So an extension of `s` is unique on von Neumann
   regular elements, and on a von Neumann regular ring it is unique when it exists.
4. On `F_3[C_3] = F_3[x]/(x-1)^3` the state is unique. Rank functions realize exactly the values
   `N(x - 1) ∈ [0, 2/3]`: the modules `F_3[x]/(x-1)^j` for `j = 1, 2, 3` give `0, 1/2, 2/3`, and Frobenius
   with nullity gives the upper bound. Here `rho^s(x-1) = 0` and `rho_s(x-1) = 1`.

**Consequence for the state upgrade.**
- **What a state pins.** On `S_- = eps_- F_3[G_3]` a state is the lifted trace on finite subgroups of
  `E⋊V`, and part 3 pins every regular element of those algebras.
- **What it leaves free.** Part 4 shows it pins nothing about `x - 1` for `x` of order three.
- **Where that lands.** Every root element `x_ij(1)` of `G_3` has order three. So step (U1) of
  `ternary-anti-central-states-force-nontrivial-rank-models` must supply exactly the Jordan-type data
  that the rank gate studies: `N(x_12(1) - 1)` and the two-root products.

Proof: route `state-pinned-regular-element-ranks-proof`.
