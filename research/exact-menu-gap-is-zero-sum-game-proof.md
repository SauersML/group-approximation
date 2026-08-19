---
rg: 2
id: exact-menu-gap-is-zero-sum-game-proof
kind: route
title: Apply finite minimax to the profile-relator rejection matrix
target: exact-menu-gap-is-zero-sum-game
requires: []
---

View `R` as the payoff matrix of a finite two-player zero-sum game.  The relator
player chooses a mixed column `mu`; against a pure profile `p` its expected
payoff is `sum_r mu_r R_(p,r)`.  Minimizing over profiles gives the primal
quantity in the claim.  The finite minimax theorem exchanges max and min and
gives the displayed dual over mixed profiles `lambda`.

If some profile rejects no exact relator, its row is zero and `gamma*=0`.
Conversely, if every row contains a `1`, the uniform distribution on `E` gives
at least `1/|E|` rejection mass on every row, hence `gamma*>0`.
