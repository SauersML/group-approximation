---
rg: 2
id: entropic-selectors-cap-every-lift-labelling-near-one-half-proof
kind: route
title: Expose the orientation edge by edge, bound each fixed labelling by Azuma-Hoeffding with the history bias as drift, and union-bound over the 2^N labellings
target: entropic-selectors-cap-every-lift-labelling-near-one-half
requires: []
---

The notation is that of the target claim.

## Step 1: one fixed labelling

Fix a labelling `(sigma, tau)`, which is not random. Write `tau_b = (t_b, u_b)`
with `t_b in Sigma_B` and `u_b in {0,1}`, and put `tau' = (t_b)_b`. For edge `i = (a, b)` put

```text
g_i = 1[ pi_i(sigma_a) = t_b ]                   (deterministic),
X_i = g_i * 1[ o_i(sigma_a) = u_b ]              (F_i-measurable).
```

Then `val_(U_c)(sigma, tau) = sum_i w_i X_i` and `val_G(sigma, tau') = sum_i w_i g_i`.

**Drift.** If `g_i = 0` then `X_i = 0`. If `g_i = 1`, let `t = pi_i(sigma_a)`.
The event `o_i(sigma_a) = u_b` is `{c_i(t) = sigma_a}` when `u_b = 0`, and
`{c_i(t) = the other fiber element}` when `u_b = 1`. Either way it is the event
that `c_i(t)` equals a fixed element `p` of the fiber. By the definition of
`beta_i`,

```text
m_i := E[X_i | F_(i-1)]  <=  g_i (1 + beta_i)/2  <=  g_i/2 + beta_i/2.
```

## Step 2: Hoeffding's lemma, conditional form

*Lemma.* Let `Y` be a random variable and `H` a sigma-field, with
`E[Y | H] = 0` and `alpha <= Y <= alpha + 1` for an `H`-measurable `alpha`.
Then `E[exp(lambda Y) | H] <= exp(lambda^2 / 8)` for every real `lambda`.

*Proof.* Work conditionally on `H`, so `alpha` is a constant. Here
`alpha <= 0 <= alpha + 1`, and we put `q = -alpha in [0,1]`. By convexity of
`exp`, for `y in [alpha, alpha+1]`,

```text
exp(lambda y) <= (alpha + 1 - y) exp(lambda alpha) + (y - alpha) exp(lambda (alpha + 1)).
```

Take conditional expectations and use `E[Y | H] = 0`. This gives
`E[exp(lambda Y) | H] <= (1 - q) exp(-lambda q) + q exp(lambda (1 - q)) = exp(L(lambda))`,
where `L(h) = -h q + ln(1 - q + q e^h)`. Then:

* `L(0) = 0`;
* `L'(h) = -q + r(h)`, where `r(h) = q e^h / (1 - q + q e^h)`, so `L'(0) = 0`;
* `L''(h) = r(h)(1 - r(h)) <= 1/4`.

Taylor's theorem gives `L(h) <= h^2/8`. QED.

## Step 3: Azuma for the fixed labelling

Put `Y_i = w_i (X_i - m_i)`. Then:

* `Y_i` is `F_i`-measurable;
* `E[Y_i | F_(i-1)] = 0`;
* `Y_i` lies in `[-w_i m_i, w_i (1 - m_i)]`, an interval of length `w_i` whose
  left end is `F_(i-1)`-measurable.

Apply the lemma to `Y_i / w_i` with parameter `lambda w_i`. This gives
`E[exp(lambda Y_i) | F_(i-1)] <= exp(lambda^2 w_i^2 / 8)`. Now condition
successively on `F_(M-1), ..., F_0` (the tower property):

```text
E[exp(lambda sum_i Y_i)] <= exp(lambda^2 sum_i w_i^2 / 8).
```

By Markov's inequality with `lambda = 4 t / sum_i w_i^2`,

```text
Pr[ sum_i Y_i >= t ] <= exp( -2 t^2 / sum_i w_i^2 ).
```

On the complement,

```text
val_(U_c)(sigma, tau) = sum_i w_i m_i + sum_i Y_i
                      < (1/2) val_G(sigma, tau') + (1/2) sum_i w_i beta_i + t.
```

The drift bound of Step 1 was used here. The variables `beta_i` do not depend
on `(sigma, tau)`.

## Step 4: union bound

`U_c` has `|Sigma_A|^|A| * (2 |Sigma_B|)^|B| = 2^(l|A|) 2^(l|B|) = 2^N`
labellings, and this set is the same for every orientation. By Step 3 and a
union bound, the probability that some labelling violates the inequality is at
most

```text
2^N exp(-2 t^2 / sum_i w_i^2) = 2^N 2^(-(N + k)) = 2^(-k)
```

for `t^2 = (N + k) ln 2 (sum_i w_i^2) / 2`. Maximising over labellings, and
using `val_G(sigma, tau') <= val(G)`, gives the displayed consequence for
`val(U_c)`.

For uniform weights, `sum_i w_i^2 = 1/M`. On a biregular graph,
`M = |A| D_A = |B| D_B`, so `N/M = l (1/D_A + 1/D_B)`. This is the stated form
of `t^2`.

## Step 5: the corollary and the boundary

*Corollary.* Let `W` be the event that some labelling has value
`>= 1/2 + gamma`, and let `C` be the event of the theorem. Then
`Pr[W cap C] >= theta - 2^(-k)`. On `W cap C`,

```text
1/2 + gamma <= 1/2 + beta_bar/2 + t,
```

using `val_G <= 1`. So `beta_bar >= 2 (gamma - t)`. Since `beta_bar >= 0`,
taking expectations gives the stated bound on `E[beta_bar]`.

*Killed classes.*

* **Independent rounding.** Put `F_0 = sigma(Z)` and let `F_i` add the coins of
  edge `i`. Since the coins are independent given `Z`, conditioning on
  `F_(i-1)` is the same as conditioning on `Z` for `c_i`, so `beta_i <= delta_i`.
* **Uniform orientation.** This is `delta_i = 0`.

*Boundary.* Take `F_0` trivial and `F_i = sigma(c_1, ..., c_i)`.

* For any fiber `t_i` of edge `i`, the realised conditional bias of `c_i(t_i)`
  is `<= beta_i`.
* The concave function `beta -> h((1+beta)/2)` is `1` at `beta = 0` and `0` at
  `beta = 1`, so it lies above the chord: `h((1+beta)/2) >= 1 - beta`.
* Hence `beta_i >= 1 - h_i`, where `h_i` is the realised conditional entropy of
  `c_i(t_i)`. Taking expectations, `E[beta_i] >= 1 - H(c_i(t_i) | c_(<i))`.
* By the chain rule and monotonicity,
  `sum_i H(c_i(t_i) | c_(<i)) <= sum_i H(c_i | c_(<i)) = H(c)`.
* Averaging with uniform weights gives `E[beta_bar] >= 1 - H(c)/M`.

QED.
