---
rg: 2
id: lambda-gapped-xor-sources-sqrt-rate-proof
kind: route
title: Feed the XOR Cheeger bound into AKKSTV Lemma 4.2 for the rate, and into the basic-SDP test T_eta for the gate; then rerun the product-strategy round budget n eta <= 2 eps'
target: lambda-gapped-xor-sources-cannot-feed-sqrt-rate-repetition
requires:
  - xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration
  - akkstv-expansion-parallel-repetition-bound
  - spectral-gap-no-outputs-cannot-prove-ugc
  - sdp-fixed-precision-solvable-gls
  - expansion-certified-repetition-caps-deficit-ratio
---

Notation is as in the target claim. `XC` denotes
`xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration`.

**λ conventions.** The λ-gap condition, "the constraint walk has at most one
eigenvalue `> 1 − λ`", says exactly that `λ_2(I − P) >= λ`. This is reading 1
of `akkstv-expansion-parallel-repetition-citation`. The bounds of `XC` hold
with `λ_2(I − P)` in place of `λ`, and they only get weaker when `λ_2` is
lowered to `λ`. So they hold for every λ-gapped instance with its parameter `λ`.

## Item 1

Let `U` be a bipartite XOR game with `opt(U) <= 1 − γ` and question gap `λ`.
`akkstv-expansion-parallel-repetition-bound` imports, verbatim (route
`akkstv-expansion-parallel-repetition-citation`), the following results.

* Theorem 4.1: "For every bipartite unique game U, ω(U) ≤ σ(U)."
* Lemma 4.2: "If σ(U) = 1 − η then the value of the SDP in Figure 1 is at least
  1 − 2η."

Write `σ(U) = 1 − η_FL`. By Lemma 4.2, the Figure 1 SDP value is
`>= 1 − 2η_FL`, so its deficit is `<= 2η_FL`. At `k = 2`, item 3 of `XC`
bounds that deficit below by `sqrt(λ) γ/27`. Hence `η_FL >= sqrt(λ) γ/54`.
Reading 4 of that route gives

```text
opt(U^(⊗r))  <=  ω(U)^r  <=  σ(U)^r  <=  (1 − sqrt(λ) γ/54)^r .
```

The base is in `[0,1]`: `sqrt(λ) γ/54 <= sqrt 2/54`. `square`

## Item 2 (XOR source gate)

Use the algorithm `T_η` of `spectral-gap-no-output-kill-proof`, section (6),
as run in item 1 of `expansion-certified-repetition-caps-deficit-ratio-proof`.
It solves the basic SDP at `k = 2` to additive precision `η/3`, through
`sdp-fixed-precision-solvable-gls`, in time `poly(Z)`. It accepts iff the
returned feasible `X*` has `obj(X*) >= 1 − 1.5 η`.

* **YES.** `val >= 1 − η` gives `sdp >= 1 − η`, so `obj(X*) >= 1 − 4η/3`, and
  `T_η` accepts.
* **NO.** Let `G` be λ-gapped with `val(G) <= 1 − γ`, and suppose `T_η`
  accepts. `X*` is a feasible basic-SDP solution with deficit `<= 1.5 η`. By
  item 3 of `XC`, and the construction in its route (`x_u = (u_1 − u_2)/sqrt(N)`),
  there are unit vectors with XOR deficit `δ(x) <= 1.5 η`. By item 1 of `XC`,
  `γ <= 1 − val(G) <= 27 · 1.5 η/sqrt(λ) = 40.5 η/sqrt(λ)`. This contradicts
  `γ > 40.5 η/sqrt(λ)`, so `T_η` rejects.

So `T_η` decides `S`, and if `S` is NP-hard then `P = NP`. `square`

## Item 3 (rate class)

Take the round budget and the Bernoulli step verbatim from item 2 of
`expansion-certified-repetition-caps-deficit-ratio-proof`. They use only
`ε' = 1 − (1 − η)^n <= 1/2` and `ψ ∈ [0,1]`, and they give `nη <= 2ε'` and
`1 − δ' <= nψ`. With `sqrt(λ) γ <= 40.5 η` from item 2,

```text
1 − δ'  <=  n (K γ² + κ sqrt(λ) γ)  <=  (2ε'/η)(K γ² + 40.5 κ η)  =  2ε' (K γ²/η + 40.5 κ).
```

Dividing by `ε'` gives `R <= 2Kγ²/η + 81κ`. For item 1's rate, `K = 0` and
`κ = 1/54`, so `R <= 1.5`. Sqrt-scale hardness and UGC both need `R`
unbounded, as recorded in items 3 of `expansion-certified-repetition-caps-deficit-ratio`.
`square`

## Item 4 (survivor conditions)

Take a λ-gapped source of any alphabet, with a pure rate `ψ <= κ sqrt(λ) γ`.

* The same budget gives `R <= nψ/ε' <= 2κ sqrt(λ) γ/η`. So `R` unbounded
  forces `sqrt(λ) γ/η` unbounded.
* At alphabet 2 this contradicts item 2. So `k >= 3`.
* At any alphabet `k`, `T_η` runs in polynomial time and accepts every YES
  instance. If it also rejected every NO instance, `S` would be in P. So, under
  `P != NP` with `S` hard, some NO host has a basic-SDP solution of deficit
  `<= 1.5 η`. With the first bullet,
  `δ_sdp/(sqrt(λ) γ) <= 1.5 η/(sqrt(λ) γ) <= 3κ/R` on that host, which tends to
  0 along any family with `R -> ∞`.

A fixed-`k` inequality `δ_sdp >= c_k sqrt(λ) γ` would then bound
`R <= 3κ/c_k` at alphabet `k`. `square`
