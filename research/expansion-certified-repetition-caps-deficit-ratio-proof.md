---
rg: 2
id: expansion-certified-repetition-caps-deficit-ratio-proof
kind: route
title: Run the r = 1 spectral-gap SDP test on the NO sources to force lambda gamma <= 1592 eta, then charge the certified rate against the product-strategy round budget n eta <= 2 eps'
target: expansion-certified-repetition-caps-deficit-ratio
requires:
  - spectral-gap-no-outputs-cannot-prove-ugc
  - sdp-fixed-precision-solvable-gls
  - akkstv-expansion-parallel-repetition-bound
---

Notation is as in the target claim. All parameters `η, γ` of a source are
rational.

## Item 1 (source gate)

Take the algorithm `T_η` from the proof of item 2 of
`spectral-gap-no-outputs-cannot-prove-ugc` (route
`spectral-gap-no-output-kill-proof`, section (6)), with `eps0 = η`. `T_η`
solves the basic SDP through `sdp-fixed-precision-solvable-gls` to additive
precision `η/3`. It uses the inner ball `r = 1/k` and the outer ball
`R = 2Nk`. It accepts iff the returned feasible `X*` has
`obj(X*) >= 1 − 1.5 η`. That route verifies the running time, `poly(Z)` for
every alphabet size `k`. The time bound and the solver input do not depend on
`r`, `γ` or `δ`. Only the correctness paragraph uses item 1.

Suppose `γ > 1536 η/λ + 28 η`.

* **YES.** If `val(G) >= 1 − η`, then `sdp(G) >= 1 − η`, so
  `obj(X*) >= 1 − 4η/3` and `T_η` accepts.
* **NO.** Let `G` be a NO instance: λ-gapped, with `val(G) <= 1 − γ`. Suppose
  `T_η` accepts. Then `sdp(G) >= obj(X*) >= 1 − 1.5 η`, so the SDP deficit is
  `ε <= 2η`. Apply item 1 of `spectral-gap-no-outputs-cannot-prove-ugc` with
  `r = 1` and its `γ` equal to our `λ`. The hypothesis "at most one eigenvalue
  `> 1 − λ`" is exactly λ-gappedness, and for `r = 1` the last term is
  dropped. This gives

  ```text
  val(G)  >=  1 − 768 ε/λ − 14 ε  >=  1 − 1536 η/λ − 28 η  >  1 − γ,
  ```

  which contradicts `val(G) <= 1 − γ`. So `T_η` rejects.

Therefore `T_η` decides `S` in polynomial time. If `S` is NP-hard, then
`P = NP`.

For the second sentence of item 1: a game with at least two vertices has at
least two walk eigenvalues, all of them `>= −1`. If `λ > 2`, then all of them
are `> 1 − λ`, so no game is λ-gapped. Hence `λ <= 2`, and `28 η <= 56 η/λ`.
Under `P != NP` a hard source has `γ <= 1536 η/λ + 28 η <= 1592 η/λ`, that is,
`λγ <= 1592 η`. `square`

## Item 2 (rate class)

Assume `P != NP` and that `S` is hard, so `λγ <= 1592 η` by item 1.

* **Round budget.** This is the computation of `black-box-repetition-sqrt-scale-proof`,
  Part 2, which uses no universal bound. From `(1 − η)^n = 1 − ε'` with
  `ε' <= 1/2` we get `n ln(1/(1−η)) = ln(1/(1−ε'))`. We also have
  `ln(1/(1−η)) >= η`, and `−ln(1−x) <= 2x` on `[0, 1/2]`, because the convex
  function `−ln(1−x)` lies below its chord, whose slope is `2 ln 2 <= 2`.
  Hence `nη <= 2ε'`.
* **Bernoulli.** For `ψ in [0,1]` and `n >= 1`, `(1 − ψ)^n >= 1 − nψ`. So
  `1 − δ' = 1 − (1 − ψ)^n <= nψ`.
* **Combine.**

  ```text
  1 − δ'  <=  n (K γ^2 + κ λγ)  <=  n (K γ^2 + 1592 κ η)
          <=  (2ε'/η)(K γ^2 + 1592 κ η)  =  2ε' (K γ^2/η + 1592 κ).
  ```

  Divide by `ε' > 0` to get `R <= 2Kγ^2/η + 3184κ`. `square`

## Items 3 and 4

**Item 3.** Put `K = 0`, so `R <= 3184κ`. The target
`Gap-UG[1 − ε', 1 − C'·sqrt(ε')]` has `R = C'/sqrt(ε')`, and
`Gap-UG[1 − ε', ε']` has `R = (1 − ε')/ε'`. The stated thresholds are these
two equations solved against `3184κ`.

* `sqrt-scale-unique-games-hardness` asks for every `C'`, at deficit ratio
  `C'/sqrt(η')`.
* `unique-games-conjecture` asks for every `ε' → 0`.

Both need `R` unbounded, and no fixed `κ` gives that. The padding line is
`R = 2`, by item 2 of `ug-hardness-deficit-ratio-padding-line`.

**Item 4.** From `R* <= R <= 2Kγ^2/η + 3184κ` we get
`γ^2 >= (R* − 3184κ)η/(2K)`. Item 1 then gives
`λ <= 1592 η/γ <= 1592 sqrt(η)/C`.

A reduction to `Gap-UG[1 − η, 1 − γ]` with `γ >= C sqrt(η)` is also a
reduction to `Gap-UG[1 − η, 1 − C sqrt(η)]`: the NO set only grows, and
`C sqrt(η) <= γ <= 1`. Restricting NO hosts to gap `O(sqrt(η))` only
strengthens the hypothesis. When the source alphabet is fixed, the source is
therefore an instance of the statement of `sqrt-scale-unique-games-hardness`
at constant `C`. `square`

## Item 5 (certificate class)

Assume `S` is hard, and let `τ > 0` be rational. Suppose, for contradiction,
that `β(G) <= 1 − η − 3τ` for every NO instance `G`. Compute `β̃(G)` with
`|β̃ − β| <= τ` in polynomial time, and accept iff `β̃ >= 1 − η − τ`.

* **YES.** `β >= val >= 1 − η` (the case `m = 1`), so `β̃ >= 1 − η − τ` and
  the algorithm accepts.
* **NO.** `β̃ <= 1 − η − 2τ`, so the algorithm rejects.

This decides `S`, so `P = NP`. Hence, under `P != NP`,
`sup_(NO) β > 1 − η − 3τ` for every rational `τ > 0`, which gives
`sup_(NO) β >= 1 − η`. So `δ' = (sup_(NO) β)^n >= (1 − η)^n = 1 − ε'`. The
certified gap `(1 − ε', δ')` is empty. `square`

## Item 6 (members)

**AKKSTV Theorem 4.3.** By `akkstv-expansion-parallel-repetition-bound`,
consider a bipartite NO instance `U` with `val(U) <= 1 − γ` and question-graph
gap `λ`. Set `γ0 = min(γ, 1/e)`. Then `val(U) <= 1 − γ0`, and `γ0 <= 1/e`, so
the cited bound gives

```text
val(U^(⊗n))  <=  (1 − c_R λ γ0/ln(1/γ0))^n .
```

The rate `ψ_A = c_R λ γ0/ln(1/γ0)` lies in `[0,1]`, as in reading 3 of the
citation route. Also `ln(1/γ0) >= 1`, so `ψ_A <= c_R λ γ0 <= c_R λγ`. The
λ of that claim is `1 − λ_2(walk)`, which is our λ-gap parameter (reading 1).
So `ψ_A` is a `Rate(0, c_R)` certificate, and item 3 caps it at
`R <= 3184 c_R`.

**Rate shapes.** For every `a >= 1` and `λ <= 2`,
`poly(λ)·γ = O(λ^a γ) <= O(2^(a−1) λγ)`. A universal `Bγ^2` rate is `Rate(B, 0)`.
`square`

## Numerical sanity check

`experiments/ugc-expansion-repetition-2026-09-17/check_rate_class_bounds.py`
checks the Bernoulli step, the round budget and the final ratio bound on a
grid, with `275400` ratio points. It finds no violation, and its output is
recorded in `output.txt`. At the gate, the largest certified ratio it finds is
`2.59` for `κ = 1` and `2.56` for the AKKSTV-shaped rate with `c_R = 1/2`.
Both are far below the proved worst case `3184κ`: the constants are not
optimised. This check is not part of the proof.
