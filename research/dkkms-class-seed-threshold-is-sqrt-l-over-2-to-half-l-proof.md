---
rg: 2
id: dkkms-class-seed-threshold-is-sqrt-l-over-2-to-half-l-proof
kind: route
title: Write the class posterior as a product of per-block likelihood factors of mean 1, average over GL_l to turn the MAP seed mass into E_ref max of H mean-one products, bound that by the second moment (1 + c)^k, and redo Lemma ID with Bernstein using the 12 * 2^(-l) variance of kept blocks
target: dkkms-class-seed-threshold-is-sqrt-l-over-2-to-half-l
requires:
  - dkkms-2to1-value-is-at-least-seed-concentration
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - dkkms-seed-law-is-uniform-in-regime-and-far-in-window
artifacts:
  - experiments/dkkms-seed-threshold-2026-09-17/check_seed_threshold.py
---

The notation is that of the target.

## Step 0: premises

- **(P1) The column model.** This is Step 7 of
  `dkkms-2to1-value-is-at-least-seed-concentration-proof`, the route of an
  ESTABLISHED node. Fix `U`. Draw `V` block by block, independently: kept with
  probability `1 - beta`, otherwise smoothed with variable `v ~ nu_i`. Then
  draw `t_1..t_(l-1)` uniform in `X_V` and `t_l` uniform in `X_U`. Put
  `Tbar = (pi t_1, ..., pi t_l)` in `Y^l`, and let `E` be the event that
  `Tbar` is linearly independent.
  - On `E`, the class is `Lbar = span Tbar` and the seed is `Tbar(ker psi0)`,
    with `psi0 = (0,..,0,1)`.
  - `Pr[not E] <= a`.
  - The model conditioned on `E` is at total variation `<= a` from the
    paper's edge law, for `k >= l`.
  - Given `V`, the block components of `Tbar` are independent across blocks.
    In a kept block, the `l` images are i.i.d. uniform in `Y_i`. In a smoothed
    block with variable `v`, the first `l - 1` images are `c_j ebar_v`, with
    `c` uniform in `F_2^(l-1)`, and the last image is uniform in `Y_i`.

  The only change from that Step 7 is that `v` has any law `nu_i`, not the
  uniform one. Step 7 never uses which variable is kept.
- **(P2) Theorem LV** of `dkkms-2to1-value-is-at-least-seed-concentration`:
  `val >= 1 - xi - mu_sp` on every triple-simple instance.
- **(P3) Theorem W** of `dkkms-seed-law-is-uniform-in-regime-and-far-in-window`:
  `TV(P0, Q) >= 1 - (1-beta)^k - 3k 4^(1-l)`, against every transitive law.
- **(P4) Bernstein's inequality.** Let `X_i` be independent, with
  `|X_i - E X_i| <= R` and `sum Var X_i <= sigma^2`. Then
  `Pr[sum (X_i - E X_i) <= -s] <= exp(-s^2 / (2(sigma^2 + R s/3)))`.

## Step 1: the model density and the class posterior

Let `rho` be the reference law: `Tbar` has `l` i.i.d. uniform columns in `Y`.
Write `M_i in Y_i^l` for the block-`i` images. For a subspace `W <= Y_i` put

```text
r_i(W) := 1 - beta + beta 2^(l-1) sum_v nu_i(v) 1{W <= <ebar_v>}.
```

- **Kept block.** `M_i` is uniform, so its density is `1`.
- **Smoothed block with variable `v`.** A matrix whose first `l - 1` columns
  lie in `<ebar_v>` has probability `2^(-(l-1)) * 4^(-1)`, against `4^(-l)`
  under `rho`. So its density is `2^(l-1) 1{M_i(ker psi0) <= <ebar_v>}`, because
  `ker psi0` is spanned by the first `l - 1` unit vectors.

Mixing over `V`, independently across blocks by (P1), shows that the model law
of `Tbar` has density `Phi(Tbar(ker psi0))` against `rho`, where for a
subspace `Q <= Y` we put `Phi(Q) := prod_i r_i(pi_i(Q))`. Put
`Phi_psi(T) := Phi(T(ker psi))` for nonzero `psi` in `(F_2^l)^*`.

**Posterior.** Fix an `l`-space `Lbar <= Y`. Every basis `T'` of `Lbar` has the
same `rho`-mass `|Y|^(-l)`, so its model mass is `|Y|^(-l) Phi(T'(ker psi0))`.
`GL_l(F_2)` acts simply transitively on the bases and transitively on the
hyperplanes `T'(ker psi0)`. So every hyperplane `Q` of `Lbar` is
`T'(ker psi0)` for the same number `|GL_l|/H` of bases, and

```text
w_model(Q | Lbar) = Phi(Q) / sum_(Q' hyperplane of Lbar) Phi(Q').
```

If the denominator vanishes, which can happen only at `beta = 1`, then `Lbar`
has model mass `0`.

## Step 2: GL-averaging

Put `h(T) := max_psi Phi_psi(T) / sum_psi Phi_psi(T)`, and `h := 0` when the
sum is `0`. On `E`, `psi -> Tbar(ker psi)` is a bijection onto the hyperplanes
of `Lbar`. So `h(Tbar) = max_Q w_model(Q | Lbar)` there, by Step 1.

For `g in GL_l`, the map `T -> Tg` (recombining columns) is a bijection of
`Y^l`, so it preserves `rho`. Also `(Tg)(ker psi) = T(ker(psi g^(-1)))`, so
`Phi_psi(Tg) = Phi_(psi g^(-1))(T)` and `h(Tg) = h(T)`. Hence

```text
E_model[h] = E_rho[Phi_psi0 h] = E_rho[Phi_(psi0 g^(-1)) h]   for every g.
```

As `g` runs over `GL_l`, the functional `psi0 g^(-1)` is uniform on the `H`
nonzero functionals. Averaging gives

```text
E_model[h] = E_rho[ (1/H) sum_psi Phi_psi * h ] = (1/H) E_rho[ max_psi Phi_psi ].      (1)
```

## Step 3: moments under rho

Fix `psi`, and pick a basis `u_1..u_(l-1)` of `ker psi` together with `u_l`
outside it. The matrix `[u]` is in `GL_l`, so the columns of `T[u]` are i.i.d.
uniform under `rho`. Hence `pi_i(T(ker psi))` is the span of `l - 1` i.i.d.
uniform vectors of `Y_i`, independently over `i`. Such a span lies in a fixed
line `<ebar_v>` with probability `2^(1-l)`, and in two different lines (so it
is `0`) with probability `4^(1-l)`. Put `X := sum_v nu_i(v) 1{span <= <ebar_v>}`.
Then:

```text
E r_i   = 1 - beta + beta 2^(l-1) 2^(1-l) = 1,
4^(l-1) E X^2 = 2^(l-1) s_i + (1 - s_i),       Var(2^(l-1) X) = (2^(l-1) - 1) s_i,
E r_i^2 = 1 + c_i,        E_rho Phi_psi = 1,        E_rho Phi_psi^2 = prod_i (1 + c_i) = 1 + chi.
```

Part (a) of the artifact checks these by exact enumeration.

## Step 4: the maximum, and Theorem F

Write `Phi_psi` for `Phi_psi(T)` with `T ~ rho`. By Step 3, `sum_psi E(Phi_psi - 1)^2 = H chi`
and `sum_psi E Phi_psi^2 = H (1 + chi)`.

- **(i)** `max_psi Phi_psi <= 1 + max_psi |Phi_psi - 1| <= 1 + sqrt(sum_psi (Phi_psi - 1)^2)`.
  By Jensen, `E_rho max_psi Phi_psi <= 1 + sqrt(H chi)`.
- **(ii)** For `x >= 0` and `tau > 0`, `x <= tau/2 + x^2/(2 tau)`. So
  `max_psi Phi_psi <= tau/2 + sum_psi Phi_psi^2/(2 tau)`, and
  `E_rho max_psi Phi_psi <= tau/2 + H(1+chi)/(2 tau) = sqrt(H(1+chi))` at
  `tau = sqrt(H(1+chi))`.

By (1), `E_model h <= min(1/H + sqrt(chi/H), sqrt((1+chi)/H)) <= M`. (The
second term is half the one in `M`, so `M` is not tight.)

**Transfer to the paper's law.** Fix `U`; `xi` is an average over `U`, so it
suffices to bound, for each `U` and each class function `P`, the paper's
`Pr[P(C) = Q | U]`. By (P1), with `k >= l + 1` so that `a <= 1/2`,

```text
Pr_paper[P(C) = Q | U] <= Pr_model[P(Lbar) = Q | E] + a <= Pr_model[P(Lbar) = Q, E]/(1 - a) + a.
```

On `E`, given `Lbar`, the model seed is `Q` with probability `w_model(Q | Lbar)`
(Step 1), so `Pr_model[P(Lbar) = Q, E] <= E_model[h 1_E] <= E_model h <= M`.
Taking the sup over `P` gives `1 - xi <= M/(1-a) + a`. This is Theorem F.

**Corollary F1.** If `k ln(1 + max_i c_i) <= ln(delta^2 H/4)` then
`1 + chi = prod_i (1 + c_i) <= delta^2 H/4`, so `2 sqrt((1+chi)/H) <= delta`.
In the uniform reading `c_i = beta^2 (2^(l-1) - 1)/3` and `ln(1 + c) <= c`,
which gives the displayed sufficient condition. Since
`k beta^2 (2^(l-1) - 1)/3 <= k beta^2 2^l / 6 = t^2 l / 6`, the condition
`t^2 <= 6 ln(delta^2 H/4)/l` also suffices. For fixed `delta`,
`ln(delta^2 H/4)/l -> ln 2`, and `sqrt(6 ln 2) = 2.039`.

## Step 5: Lemma B

Use the notation of Step 8 of the seed-concentration route: `Z_i(psi)`,
`D_i = Z_i(psi0) - Z_i(psi)` for a fixed competitor `psi != psi0`, and `m` the
number of smoothed blocks. The facts proved there do not depend on the law of
the smoothed variable, so they hold for every `nu_i`:

- given `V`, the `D_i` are independent;
- a kept block has `E D_i = 0`;
- a smoothed block has `Z_i(psi0) = 1`, so `D_i = 1 - Z_i(psi)` is a Bernoulli
  variable with mean `Delta_l`.

**Variances.** In a kept block, `Z_i(psi) = 1` iff the span of `l - 1` i.i.d.
uniform vectors of `Y_i` is at most a line (Step 3). The three lines each hold
the span with probability `2^(1-l)`, and all three hold it only when it is `0`,
with probability `4^(1-l)`. So `Pr[Z_i = 1] = 3*2^(1-l) - 2*4^(1-l) <= 6*2^(-l)`.
Since `D_i^2 = |Z_i(psi0) - Z_i(psi)| <= Z_i(psi0) + Z_i(psi)`,
`Var D_i <= 12*2^(-l)`. In a smoothed block, `Var D_i <= 1/4`. Every block has
`|D_i - E D_i| <= 1 <= 2 =: R`. So `sigma^2 := 12 k 2^(-l) + m/4` works.

**Tail.** The rule errs against `psi` only if `sum_i D_i <= 0` (ties count as
errors). Apply (P4) with `s = m Delta_l`. Since `Delta_l <= 1/2`,
`R s/3 <= m/3`, and

```text
Pr[sum D_i <= 0 | V] <= exp( - m^2 Delta_l^2 / (24 k 2^(-l) + m/2 + 2m/3) ) = exp( - m^2 Delta_l^2 / (24 k 2^(-l) + 7m/6) ).
```

The exponent `m^2/(A + B m)` increases in `m > 0`. At `m >= beta k/2` it is at
least `(beta^2 k^2/4) Delta_l^2 / (24 k 2^(-l) + 7 beta k/12) = beta^2 k Delta_l^2 / (96*2^(-l) + 7 beta/3)`.
Also `Pr[m < beta k/2] <= exp(-beta k/8)`, since `m` is Binomial`(k, beta)`.
A union over the `2^l - 2` competitors gives `Pr_model[P* != Q, E] <= eps_B`.

As in Step 4, the paper's error is at most `eps_B/(1-a) + a`. Since `P*` is a
class function, `xi = 1 - sup_P Pr[P(C) = Q] <= Pr[P* != Q] <= eps_B/(1-a) + a`.
Here `l >= 3` is needed only for `Delta_l > 0`.

**Explicit form.** Put `X := beta^2 k Delta_l^2 / (96*2^(-l) + 7 beta/3)`. The
denominator is at most twice its larger term.

- If `96*2^(-l) >= 7 beta/3`, then `X >= beta^2 k Delta_l^2 2^l / 192`.
- Otherwise `X >= 3 beta k Delta_l^2 / 14`.

Under the first two terms of the stated maximum, `X >= ln(2^l/eps)` in both
cases. So `(2^l - 2) e^(-X) < eps`. The third term gives `exp(-beta k/8) <= eps`.
Hence `eps_B < 2 eps`. In the scaled variable, `beta^2 k 2^l = t^2 l`, so the
first term reads `t^2 >= 192 ln(2^l/eps)/(Delta_l^2 l)`. For fixed `eps` this
tends to `768 ln 2`, and `sqrt(768 ln 2) = 23.07`.

## Step 6: Corollaries SC' and TH

**SC'.** Suppose `val <= delta` on a triple-simple instance. By (P2),
`xi >= 1 - delta - mu_sp`. By Lemma B and `a <= 1/3`,
`xi <= (3/2) eps_B + a`. So `(3/2) eps_B >= 1 - delta - mu_sp - a >= 3(1 - delta)/4`,
that is, `eps_B >= (1 - delta)/2`.

Now suppose `beta` is at least the stated maximum. Take `eps := (1 - delta)/4`.
Then `ln(2^l/eps) = Lambda` and `ln(1/eps) = ln(4/(1-delta))`, so the explicit
form of Lemma B gives `eps_B < 2 eps = (1 - delta)/2`. This is a contradiction,
so `beta` is below the maximum.

For the O-form, use `Delta_l >= 1/4` (`l >= 3`) and
`Lambda = (l + 2) ln 2 + ln(1/(1-delta))`. Multiplying by `sqrt(k)`, the first
term is `O(sqrt(Lambda) 2^(-l/2))` and the other two are `O(Lambda/sqrt(k))`.
At `k >= l 2^l` the latter are `O(sqrt(l) 2^(-l/2))` for fixed `delta`.

**TH, lower half.** Fix `delta`. Read `t <= 2.03 (1 - o(1))` as
`t^2 <= 6 ln(delta^2 H/4)/l`. The right side tends to `6 ln 2 = 2.039^2`, and it
is positive once `delta^2 H > 4`. By F1, `1 - xi <= delta/(1-a) + a`. For
`a <= 1/2`, `1/(1-a) <= 1 + 2a`, so `1 - xi <= delta + 3a`.

**TH, upper half.** Fix `eps`. Read `t >= 23.1 (1 + o(1))` as
`t^2 >= 192 ln(2^l/eps)/(Delta_l^2 l)`, which is the first term of Lemma B.
For the other two terms: `beta k = t sqrt(l k 2^(-l)) >= t l sqrt(C)` when
`k >= C l 2^l`, and `t >= 23`. Using `Delta_l^2 >= 1/16`,

```text
14 ln(2^l/eps)/(3 Delta_l^2) + 8 ln(1/eps)  <=  52 l + 83 ln(1/eps)  <=  l (52 + 83 ln(1/eps)).
```

So `C(eps) := (3 + 4 ln(1/eps))^2` is enough, since then
`23 sqrt(C) >= 69 + 92 ln(1/eps)`. Lemma B gives `xi <= 2 eps/(1-a) + a`. With
`a <= 1/3`, this is `<= 3 eps + a`, and (P2) gives the value bound.

The ratio of the two thresholds is `sqrt(768 ln 2)/sqrt(6 ln 2) = sqrt(128) = 11.31 < 12`.

## Step 7: Corollary D

Let `l >= 6` and `2^l >= 8/delta^2 + 1`. Then `H >= 8/delta^2`, so
`L_d := ln(delta^2 H/4) >= ln 2`.

- **Non-empty.** `k_T(l) = 4^(l-1)/12 >= 2^l` iff `2^(l-2) >= 12`, which holds
  for `l >= 6`. At `k = 2^l` and `beta = 2/k`, the upper constraint reads
  `4 (2^(l-1) - 1) <= 3 * 2^l L_d`. The left side is below `2^(l+1)`, and
  `3 L_d >= 3 ln 2 > 2`.
- **Property 1.** The upper constraint on `beta` is exactly the uniform-reading
  condition of F1, and `k >= 2^l >= l + 1`.
- **Property 2.** By (P3), `TV >= 1 - (1-beta)^k - 3k 4^(1-l)`. Here
  `(1-beta)^k <= e^(-beta k) <= e^(-2)` and `3k 4^(1-l) <= 3 k_T 4^(1-l) = 1/4`.
  So `TV >= 1 - e^(-2) - 1/4 = 0.6147`. (P3) needs only `k >= l - 1`.
- **Property 3.** `beta sqrt(k) >= 2/sqrt(k) >= 2/sqrt(k_T) = 8 sqrt(3) 2^(-l)`.
  So `beta sqrt(k) 2^(l+3) >= 64 sqrt(3)`. Since
  `SD* = beta sqrt(k) 2^(l+3) + 3*2^(l-k)` (outer-honest node), `SD* > 10^(-5)`
  and the point is outside (R).
- **Property 4.** Take `beta = ln ln k / k`. The lower constraint is
  `ln ln k >= 2`, that is, `k >= e^(e^2)`. The upper constraint reads
  `(ln ln k)^2 (2^(l-1) - 1) <= 3 k L_d`. Since `3 L_d > 2`, it suffices that
  `k >= 2^(l-2) (ln ln k)^2`, which the hypothesis `k >= 2^l (ln ln k)^2` gives.
  That hypothesis also gives `k >= 2^l`.

**The window.** `f(k) = k/(ln ln k)^2` increases for `k >= e^e`, because
`f'` has the sign of `ln k ln ln k - 2`. So it suffices to check both conditions
at `k = k_A(l) = e^l (2 l ln 2 + ln(4*192^2))`. Part (d) of the artifact
checks `k_A(l) >= max(e^(e^2), 2^l (ln ln k_A)^2)` for every `20 <= l < 200`.
For `l >= 200`, `ln k_A <= 2l`, so it follows from `k_A >= e^l` and
`(e/2)^l >= (ln(2l))^2`.
The window is non-empty for `l >= 20` (Theorem W). So for `l >= 20`, and `l` large
enough for the `delta` condition, every `k` in `[k_A(l), k_T(l)]` at the
published rate lies in the band.
