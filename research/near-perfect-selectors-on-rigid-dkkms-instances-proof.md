---
rg: 2
id: near-perfect-selectors-on-rigid-dkkms-instances-proof
kind: route
title: Proof that near-perfect selectors on DKKMS instances in the covering regime put the source problem in RP
target: near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp
requires:
  - dkkms-near-perfect-labellings-are-outer-honest
  - high-advantage-selector-witnesses-decode-good-outer-labellings
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - orientation-lifts-sandwich-2to1-game-values
artifacts:
  - experiments/ugc-seed-law-2026-09-17/check_seed_law_regime.py
---

Notation is that of the target. The edge set of `G_folded(I)` is the set of
copies `e = ((C, U, L), (V, L'))` of `G_multi(I)` edges, with the edge law `mu`
of the DKKMS process restricted to `L meet H_U = {0}`. A labelling of
`G_folded` gives each class `C` a class label `sigma_C` and each B-vertex a
linear `B(V,L')`. Its value is the `mu`-mass of copies where the unfolding of
`sigma_C` at `(U,L)`, restricted to `L'`, equals `B(V,L')`. This is exactly a
labelling `(A, B)` of `G_multi` in the sense of Theorem R, with
`A(U,L) = (sigma_C)~_U|_L`, and the two values coincide (item 1 of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`: unfolding is a
bijection `Fun(R_C) -> Fun(L)`).

## Step 0. Regime bookkeeping

Let `(l,k)` satisfy (R): `l >= 3` and `SD* <= 10^(-5)`.

* `SD* >= beta sqrt(k) 2^(l+3)` gives `2^(l-1) beta <= 10^(-5) / (16 sqrt k) <= 1/8`.
* `SD* >= 3 * 2^(l-k)` gives `2^(l-k) <= 10^(-5)/3 <= 1/200`.
* `2^(l-k) <= 1/200 < 1/4` gives `k >= l + 3`, hence `3k >= l + 2`.

So every hypothesis of Theorem R holds. Condition (A) is verbatim the
hypothesis on `(l,k)` of Corollary A of
`high-advantage-selector-witnesses-decode-good-outer-labellings`, and it is
what Theorem 3 needs on the NO side (Step 4).

## Step 1. Forget the right bit

Fix a YES input `x`, an outcome `o = S(x)` of the selector with
`val(U_o) >= 1 - xi`, `xi := 10^(-5)`, and an optimal lift labelling `W` of
`U_o = U_o(G_folded(I(x)))`. `W` gives each class a label `sigma_C` and each
B-vertex a pair `(B(V,L'), b(V,L'))`.

By construction of the lift (`orientation-lifts-sandwich-2to1-game-values`),
each lifted constraint on `e` accepts `(sigma_C, (tau, b))` only if the 2-to-1
constraint on `e` accepts `(sigma_C, tau)`. Every lifted constraint *implies*
its 2-to-1 constraint. So the forgetful labelling `(A, B)` (class labels of
`W`, right labels of `W` with the bit dropped) has value `>= 1 - xi` on
`G_folded`, hence on `G_multi`. Nothing about `o` or `S` is used here.

(Concretely, `U_o` carries on `e` the bijection `a -> (p_e(a), o_e(a))`, so a
satisfied lifted edge has `p_e(sigma_C) = tau`, which is the 2-to-1 constraint.)

## Step 2. Theorem R on the forgotten labelling

Apply Theorem R and Corollaries P, N of
`dkkms-near-perfect-labellings-are-outer-honest` to `(A, B)` with
`eta = xi = 10^(-5)`, which is allowed by Step 0. This gives an outer labelling
`lambda` of `Phi_k` and a choice `kappa` of class members with

* `val_(Phi_k)(lambda) >= 15/16`;
* `d_kappa(lambda) <= 1/64`;
* `(A, B)` and `hon_kappa(lambda)` agree at both endpoints outside `mu`-mass
  `<= 1/128`.

The dirt `d_kappa` of Corollary P is the same quantity as the dirt of the
decoder node: the `mu`-mass of copies at which the unfolding of
`hon_kappa(lambda)_C` differs from `lambda_U|_L`.

## Step 3. Lift the patchwork back with the bits of W

Put `b := ` the bit component of `W` and consider
`hon_kappa(lambda, b)_(V,L') = (lambda_V|_(L'), b(V,L'))`. Its class labels are
those of `hon_kappa(lambda)`. On a copy `e` outside the `1/128` set of Step 2,
`sigma_C = hon_kappa(lambda)_C` and `B(V,L') = lambda_V|_(L')`, so `W` and
`hon_kappa(lambda, b)` agree at both endpoints of `e`: they also share the bit
`b(V,L')`, by definition. Therefore `W` is a witness for `lambda` in the sense
of the decoder node, with

```text
distance zeta <= 1/128,   dirt d <= 1/64,   lift value >= 1 - xi,
xi + zeta <= 10^(-5) + 1/128 <= 1/64.
```

This holds for every outcome `o` of `S(x)` with `val(U_o) >= 1 - 10^(-5)`,
hence with probability `>= theta(|x|)` over the coins of `S`.

## Step 4. The decoder

Apply Theorem 3 of `high-advantage-selector-witnesses-decode-good-outer-labellings`
to the promise problem `Lang`, the LEC `U_o(G_folded(I(x)))` (the doubled
alphabet LEC of its section "The DKKMS instances", which checks (E) at
`tau = 2^(l-1-2k) <= 1/16`, (M=) and (B_d) there), and the selector `S`
composed with `x -> I(x)`. This composition is polynomial time.

* YES side: Step 3 with `eps = 1/16`, `xi + zeta <= 1/64`, `d <= 1/64`, so
  `c1 >= 1 - 1/8 - 8 (1/64 + 1/64) = 5/8` as computed in Corollary A.
* NO side: `val(I(x)) <= s*`, so DKKMS Lemma 5.4 gives
  `val(Phi_k) <= eps_k <= p0^2/4 < 5 p0^2/16 <= p0^2 c1 / 2`.

Theorem 3 then gives `Lang in RP`, with one-sided success
`>= theta p0^2 c1/2 >= theta 2^(-2l) / 117965`, which is `1/poly` for fixed
`l`. Its decoder never uses `lambda`, `kappa`, `W` or the views of `S`, so
nothing about `S` beyond polynomial time was used.

With `Lang = Gap3Lin(1 - eps_3, s*)` and `I(x) = x`, DKKMS Theorem 4.1 makes
`Lang` NP-hard, so `NP in RP`. This proves Theorem S.

## Corollaries

* **S1, S2.** Both holes ask for YES lift value `1 - eta'` with `eta' -> 0`.
  Once `eta' <= 10^(-5)` at a parameter point in the regime, Theorem S applies.
  For S2, the reduction `x -> D(I(x))` is the DKKMS construction after a
  polynomial-time 3LIN map, which is the case `I(x)` of Theorem S. The views
  and the parity leakage do not enter any of Steps 1 to 4.
* **S3.** Put `k_A(l) = e^(q l) ln(4/p0^2)`, so that `eps_k <= p0^2/4` iff
  `k >= k_A(l)`, and let `k_0(l)` be the least `k` with `SD*(l,k) <= 10^(-5)`.
  `SD*` is decreasing in `k` once `k >= 16`, so (A) implies (R) iff
  `k_A(l) >= k_0(l)`. Part (c) of the artifact finds that for `q = 2` this
  holds for `43 <= l < 200` and fails at `l = 42`, and that for `q = 1` it
  fails for every `3 <= l < 200`. For `l >= 199` and `q = 2`, the margin
  `log k_A - log k_0` is `97` nats at `l = 199`, with slope
  `2 - 2 ln 2 - O(1/l) > 0.6` per unit of `l`.

## The seed-law computation (reconciliation)

The artifact computes the exact law of `L'` given `(U, L)`, in closed form per
hyperplane of `L` (the formula is in its docstring). It samples only `L`. Its
parts (a) and (b) are recorded in the target. They support the reading that the
concentration seen on the bus is a large-`beta` effect. They are not used in
Steps 0 to 4, which rely only on Theorem R.
