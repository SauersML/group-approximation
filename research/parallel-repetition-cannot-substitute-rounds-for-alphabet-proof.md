---
rg: 2
id: parallel-repetition-cannot-substitute-rounds-for-alphabet-proof
kind: route
title: Solve the basic SDP on the base game, not on its repetition; product or multiplicative completeness puts YES bases at sdp >= 1 - eta, and Steurer's rounding puts every base with sdp >= 1 - 1.5 eta at repeated value >= 1 - C_1 sqrt(1.5 l eta ln k)
target: parallel-repetition-cannot-substitute-rounds-for-alphabet
requires:
  - steurer-parallel-repeated-unique-games-rounding
  - sdp-fixed-precision-solvable-gls
  - black-box-repetition-needs-sqrt-scale-soundness-gap
---

Notation is as in the target claim.

## Step 0: the base SDP test `T_η`

Fix a rational `η in (0,1)`. On input `x`, compute `G_x`. Its size `Z` is
polynomial in `|x|`, and `G_x^l` is never written down. Then run the solver of
`spectral-gap-no-output-kill-proof`, item 2 ("Solver input" and "Ball
verification"), on `G_x` with precision `η/3`:

- the solver is `sdp-fixed-precision-solvable-gls`;
- `X0 = I/k`, `r = 1/k` and `R = 2Nk`;
- the SDP is the same program `sdp` (reading 3 of the citation route).

It returns, in time `poly(Z, log(1/η))`, a feasible `X*` with
`sdp(G_x) − η/3 <= obj(X*) <= sdp(G_x)`. `T_η` accepts iff
`obj(X*) >= 1 − 1.5 η`.

- **(T-YES)** If `sdp(G_x) >= 1 − η`, then `obj(X*) >= 1 − 4η/3`, so `T_η`
  accepts.
- **(T-NO)** If `T_η` accepts, then `sdp(G_x) >= obj(X*) >= 1 − 1.5η`, and by
  (S1) with `ε = 1.5 η`:

  ```text
  opt(G_x^l)  >=  1 − C_1 sqrt(1.5 l η ln k).
  ```

## Step 1: part (a)

- **YES.** `opt(G_x) >= 1 − η` and `sdp >= opt` give `sdp(G_x) >= 1 − η`, so
  `T_η` accepts by (T-YES).
- **NO.** If `T_η` accepted, (T-NO) would give
  `opt(G_x^l) >= 1 − C_1 sqrt(1.5 lη ln k) > 1 − Γ`, which contradicts
  `x in N`. So `T_η` rejects.

`T_η` therefore decides `Pi` in polynomial time. The value `η` is hardwired.
`l` enters only through the hypothesis on `Γ`, not the algorithm. `square`

## Step 2: part (b)

- **Bound on `sdp(G_x)`.** Let `x in Y`. By (S2),
  `sdp(G_x)^l >= opt(G_x^l) >= 1 − η_out`. For `t in (0, 1/2]`, put
  `y = t/(l(1 − t))`, which lies in `[0, 1]`. Then

  ```text
  (1 − y)^l  <=  exp(−l y)  =  exp(−t/(1−t))  <=  1 − t,
  ```

  because `ln(1/(1−t)) = ln(1 + t/(1−t)) <= t/(1−t)`. Taking `l`-th roots of
  nonnegative numbers gives `(1 − t)^(1/l) >= 1 − y >= 1 − 2t/l`. So
  `sdp(G_x) >= 1 − 2η_out/l`.
- **Choice of `η`.** Put `η := 2 η_out / l`. It is rational, and its bit size is
  polynomial because `l` has polynomial bit size.
- **YES.** `T_η` accepts by (T-YES).
- **NO.** If `T_η` accepted, (T-NO) would give
  `opt(G_x^l) >= 1 − C_1 sqrt(1.5 · l · (2η_out/l) · ln k) = 1 − C_1 sqrt(3 η_out ln k) > 1 − Γ`,
  which contradicts `x in N`.

So `Pi` is in `P`. `square`

## Step 3: part (c)

In case (b), (c) is the contrapositive with `C_1 sqrt(3) <= 2 C_1`.

In case (a), `η_out = 1 − (1 − η)^l <= 1/2`. The round budget of
`black-box-repetition-sqrt-scale-proof`, Part 2 (the computation is reproduced
in `expansion-certified-repetition-caps-deficit-ratio-proof`, item 2) gives
`lη <= 2 η_out`. Unless `Pi` is in `P`, part (a) gives

```text
Γ <= C_1 sqrt(1.5 · 2 η_out ln k) = C_1 sqrt(3 η_out ln k) <= 2 C_1 sqrt(η_out ln k).
```

Divide by `sqrt(η_out)`. `square`

## Step 4: Corollary RA

**Item 1.**

- **Vacuous case.** If `C <= 2 C_1 sqrt(ln 2)`, the bound holds because
  `k >= 2`.
- **Otherwise `η_out <= 1/2`.** We have `C > 1.66`, and the hypothesis
  `η_out <= 1/C^2` gives `η_out < 1/2`.
- **Applying part (b).** The route's promise problem `Pi` is the pullback of
  the NP-hard gap, which is NP-hard. Part (b) applies with
  `Γ = C sqrt(η_out)`, and needs no product structure of completeness. If
  `C > 2 C_1 sqrt(ln k) >= C_1 sqrt(3 ln k)`, then `Pi` is in `P`, so `P = NP`.

**Item 2.** Take `η_out = ε <= 1/2` and `Γ = 1 − ε`. Part (c) gives
`1 − ε <= 2 C_1 sqrt(ε ln k)`. Square this, then use `(1 − ε)^2 >= 1/4`.

**Item 3.** Put `ε_s = 1 − sdp(G)` and `l = ⌈1/ψ⌉ <= 2/ψ`.

- **Upper bound on `opt(G^l)`.** `opt(G^l) <= (1 − ψ)^l <= exp(−ψ l) <= 1/e`.
- **Lower bound on `opt(G^l)`.** (S1) gives
  `opt(G^l) >= 1 − C_1 sqrt(l ε_s ln k)`.
- **Combining.** Together these give `C_1^2 (2/ψ) ε_s ln k >= (1 − 1/e)^2`,
  that is,

  ```text
  ψ <= (2/(1 − 1/e)^2) C_1^2 ε_s ln k,    where 2/(1 − 1/e)^2 = 5.0053... <= 5.01.
  ```

- **The case `ε_s = 0`.** The two bounds contradict each other, so no
  `ψ > 0` satisfies the hypothesis.

**Item 4.**

- **Existence of the instance.** Run `T_η` of Step 0 on the source.
  - YES instances are accepted, by (T-YES).
  - Suppose every NO instance had `sdp < 1 − 1.5 η`. Then `obj(X*) <= sdp` would
    make `T_η` reject them all, so `T_η` would decide an NP-hard problem.

  Unless `P = NP`, some NO instance `G*` therefore has `sdp(G*) >= 1 − 1.5η`.
- **The rate bound.** A rate that is valid on every NO instance is valid on
  `G*`. Item 3 then gives `ψ <= 1.5 · 5.0053 C_1^2 η ln k <= 7.51 C_1^2 η ln k`.

## Step 5: the (R2) window

Consider a rate-certified route. Its NO outputs satisfy
`opt(G^l) <= (1 − ψ)^l`, so its certified deficit is
`Γ = 1 − (1 − ψ)^l <= lψ` by Bernoulli. Its YES outputs have
`η_out = 1 − (1 − η)^l <= 1/2`.

- **Size of `lη`.** By the round budget, `lη <= 2η_out <= 1`.
- **Lower bound on `η_out`.** From `(1 − η)^l <= exp(−lη)` and the concavity of
  `1 − e^(−t)` on `[0, 1]`, we get `η_out >= (1 − 1/e) lη`.
- **Ratio.** Using `l <= 1/η`,

  ```text
  C  =  Γ / sqrt(η_out)  <=  lψ / sqrt((1 − 1/e) lη)  =  sqrt(l) ψ / sqrt((1 − 1/e) η)
     <=  ψ / (η sqrt(1 − 1/e))  =  1.2578... ψ/η.
  ```

  So `ψ/η >= 0.795 C >= 0.79 C`.

The upper end of the window is item 4. The alphabet condition (R1) is item 1.
`square`
