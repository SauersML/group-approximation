---
rg: 2
id: sqrt-scale-ug-alphabet-cost-proof
kind: route
title: Markov on the CMM rounding gives a one-sided-error test for the sqrt-scale gap once C exceeds 2A sqrt(log k)
target: sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared
requires: [cmm-unique-games-sqrt-log-k-rounding]
---

Set `a = A sqrt(eta log k)`. Since `C > 2A sqrt(log k)`, the interval
`[1 - C sqrt(eta), 1 - 2a)` is nonempty. Fix a rational `s'` in it and hardwire
it, together with `eta`, into the algorithm below.

**Algorithm.** On input a unique game `G` with edge multiset `E`:

1. Run the CMM rounding from `cmm-unique-games-sqrt-log-k-rounding`, with
   parameter `eta`.
2. Count the satisfied edges `m`, and put `X = m/|E|`.
3. Accept iff `m > s' |E|`, that is, iff `X > s'`.

This takes polynomial time.

**YES instances**, `val(G) >= 1 - eta`. By the CMM claim, `E[1 - X] <= a`. By
Markov's inequality applied to the nonnegative variable `1 - X`,
`Pr[1 - X >= 2a] <= 1/2`. If `a = 0` then `X = 1` surely. In either case
`Pr[X > 1 - 2a] >= 1/2`. Since `1 - 2a > s'`, the algorithm accepts with
probability at least `1/2`.

**NO instances**, `val(G) <= 1 - C sqrt(eta)`. Every assignment satisfies at
most that fraction, so `X <= 1 - C sqrt(eta) <= s'`. The algorithm never
accepts.

So the promise problem `Gap-UG_k[1-eta, 1-C sqrt(eta)]` is in promise-RP. If it
is NP-hard under Karp reductions, compose a reduction from SAT with this
algorithm. Satisfiable formulas map to YES instances, accepted with probability
`>= 1/2`. Unsatisfiable formulas map to NO instances, which are never accepted.
Hence `SAT` is in `RP`, and `NP <= RP`.

The contrapositive is the displayed bound. If `NP not<= RP`, then NP-hardness
at ratio `C` forces `C <= 2A sqrt(log k)`, that is,
`k >= exp(C^2/(4A^2))`. `square`
