---
rg: 2
id: dkkms-quotient-covering-proves-99-percent-rigidity-proof
kind: route
title: Descend the class labels to a linear table on Gr(X_U/H_U, l), note that the two-extension rejection and the A-side disagreement depend only on the images, show the image of the seed is uniform on Gr(W_V, l-1) given V, bound the chi-square of the mixture by Gaussian-binomial ratios, and rerun Theorem R with that distance
target: dkkms-quotient-covering-proves-99-percent-rigidity
requires:
  - dkkms-near-perfect-labellings-are-outer-honest
  - near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
artifacts:
  - experiments/dkkms-class-covering-2026-09-17/check_class_covering.py
---

The notation is that of the target. The route of
`dkkms-near-perfect-labellings-are-outer-honest` is called the OH route here.
From it this route uses Lemma 2, the invalid-mass bounds of Step 3, and
Steps 5 and 6 with Corollary P, all verbatim. It also uses the quoted inputs
(Q2), (Q4) and (Q5) of that route. The covering lemma (Q6) is not used.

## Imported statements

* **Lemma 2 (OH route, Step 2).** "Let `N >= 3` and `2 <= l <= N`. A *linear
  table* on `Gr(F_2^N, l)` is a map `F` that gives every `l`-space `L` a
  linear functional `F[L] : L -> F_2`. The *test* `T` picks a uniform
  `(l-1)`-space `L'`, then two independent uniform `l`-spaces `L_1, L_2 > L'`,
  and rejects iff `F[L_1]|_(L') != F[L_2]|_(L')`." And "one has
  `C_l <= 16 + 24 * 2^(-N) <= 19 <= 20` for every `l >= 2` and `N >= 3`. The
  same bound holds for every minimiser of `g -> Pr_L[F[L] != g|_L]`".
* **(Q5) Invariance (OH route).** "If `L_1 + H_U = L_2 + H_U` then both are
  equal to `R + H_U` and `~sigma : R + H_U -> F_2` must equal the
  `(H_U, h_U)` extension of `A(U,L_1)` as well as the `(H_U, h_U)` extension
  of `A(U,L_2)`."
* **Invalid mass (OH route, Step 3).** For `V` keeping `j` equations,
  `m = dim X_V = k + 2j` and `dim(H_U meet X_V) = j`:
  `Pr[L' meet H_U != 0] <= 2^(l-1+j-m) <= 2^(l-1-k)`, and
  `q_UV <= 2^(l-k)`.

## Step 1: the class table on the quotient

Fix `U` and a linear extension `h*_U : X_U -> F_2` of `h_U`. For example, take
`b_e` times the first coordinate of the block of `e`. For a valid `L`
(`L meet H_U = 0`) put `M = L + H_U`. Let `~sigma` be the
`(H_U, h_U)`-extension of `A(U,L)` to `M`, as in (Q4). Then `~sigma - h*_U`
vanishes on `H_U`, so it descends to a linear functional on
`Sbar := pi(L) = M/H_U`. Call it `Fbar_U[Sbar]`.

* **Well defined.** By (Q5) it depends only on `M`, which is determined by
  `Sbar = pi(L)`.
* **Total.** Every `l`-space of `Y` is `pi(L)` for a valid `L`: lift a basis.
* **Linear table.** So `Fbar_U` is a linear table on `Gr(Y, l)` with
  `N = 2k >= 3`, and `l <= 2k` because `2^(l-k) <= 1/200`.

For valid `L` and `z` in `L`,

```text
A(U,L)(z) = Fbar_U[pi L](pi z) + h*_U(z).                                     (1)
```

For a linear `g : Y -> F_2`, put `lambda_U := g o pi + h*_U`. Then
`lambda_U|_(H_U) = h_U`, so `lambda_U` satisfies every equation of `U`. By (1),
`A(U,L) = lambda_U|_L` iff `Fbar_U[pi L] = g|_(pi L)`.

## Step 2: the events are image events

Let `P` be the two-extension test of OH Step 3. Draw `(V, L', L_1)` from
`G_multi` given `U`, and draw `L_2` from the conditional law of `L` given
`(U, V, L')`, independently of `L_1`. As there, `rej_P <= 2 eta_U`, because a
rejection violates one of the two edges `((U, L_i), (V, L'))`, each of which
has the law of `G_multi` given `U`.

**Rejection is an image event.** By (1), `A(U,L_1)|_(L')` and
`A(U,L_2)|_(L')` differ by `(f_1 - f_2) o pi` on `L'`, where
`f_i = Fbar_U[Sbar_i]` and `Sbar_i = pi(L_i)`. So `P` rejects iff
`f_1|_(Qbar) != f_2|_(Qbar)`, with `Qbar = pi(L')` of dimension `l - 1`. This
is exactly the rejection of the test `T` of Lemma 2 on `Fbar_U`, evaluated at
the triple `(Qbar, Sbar_1, Sbar_2)`.

**The kernel from the seed is the ideal one.** Given `(V, L')`, the `L_i` are
independent and uniform among valid `L > L'`. Write `L = L' + <x>`. The valid
`L` are those with `x` outside `L' + H_U`, and each valid `L` arises from
exactly `2^(l-1)` choices of `x`. So `x` is uniform on `X_U \ (L' + H_U)`.

`pi` maps `X_U \ (L' + H_U)` onto `Y \ Qbar`, and every fibre has size
`|H_U|`. So `pi x` is uniform on `Y \ Qbar`, and `Sbar_i = Qbar + <pi x_i>` is
a uniform `l`-space containing `Qbar`. Hence, given `Qbar`, the pair
`(Sbar_1, Sbar_2)` has exactly the law it has in `T`.

It follows that

```text
|rej_P - rej_T(Fbar_U)|  <=  TV(mu_P, u),                                      (2)
```

where `mu_P` is the law of `Qbar` under `P`, and `u` is uniform on
`Gr(Y, l-1)`. Likewise, the law of `pi(L)` under `G_multi | U` is `mu_P`
pushed forward by the up-kernel. The uniform law pushed forward by the same
kernel is uniform on `Gr(Y, l)`. So

```text
tau_U := Pr_(G_multi | U)[A(U,L) != lambda_U|_L]  <=  Pr_(Sbar unif)[Fbar_U[Sbar] != g|_Sbar] + TV(mu_P, u).   (3)
```

## Step 3: Theorem CL

Write `d = l - 1`, `E := {L' meet H_U = 0}`, and `G(n, d) := |Gr(F_2^n, d)|`.

**The law of `(V, L')` under `P`.** In `G_multi` given `U`, the triple
`(V, L', L)` has weight proportional to

```text
P_0(V | U) * unif_(Gr(X_V, d))(L') * unif_(L > L')(L) * 1[L valid].
```

The number of `l`-spaces `L > L'` of `X_U` does not depend on `L'`. On `E` the
number of valid ones is fixed too: it is the number of `x` outside
`L' + H_U`, divided by `2^(l-1)`. Off `E` there are none. So `(V, L')` has
weight proportional to `P_0(V|U) * unif(L') * 1_E(L')`.

Hence, under `P`:

* `V` has law `rho_P(V)`, proportional to `P_0(V|U) Pr[E | V]`;
* given `V`, `L'` is uniform on `E meet Gr(X_V, d)`.

**Uniformity given `V`.** Put `K = X_V meet H_U`. For `L' < X_V`,
`L' meet H_U = L' meet K`, and `pi|_(X_V)` has kernel `K` and image `W_V`.
The block form follows because `pi` is blockwise.

* In a kept block, `pi(F_2^3) = Y_i`.
* In a block smoothed to `v`, the image is `<pi(e_v)>`, and `pi(e_v) != 0`.

The subgroup of `GL(X_V)` fixing `K` preserves the uniform law on
`E meet Gr(X_V, d)`. It maps onto `GL(X_V / K) = GL(W_V)`. So the law of
`pi(L')` is `GL(W_V)`-invariant. `GL(W_V)` is transitive on `Gr(W_V, d)`, so
the law is uniform there. Call it `p_V`. The artifact confirms this by
enumeration for `(k, d)` in `{(2,1), (3,1), (4,1), (3,2)}`.

**Removing the reweighting.** Let `mu_U := sum_V P_0(V|U) p_V`, so that
`mu_P = sum_V rho_P(V) p_V`. With `c(V) = Pr[E|V]` in `[1 - 2^(d-k), 1]` (the
invalid-mass bound) and `Z = E c <= 1`,

```text
TV(mu_P, mu_U) <= TV(rho_P, P_0(.|U)) = E (1 - c/Z)_+ <= E (1 - c) <= 2^(d-k).  (4)
```

**Chi-square.** Let `V, V'` be independent draws from `P_0(.|U)`. Then

```text
chi^2(mu_U || u) + 1 = G(2k, d) * sum_Q mu_U(Q)^2
                     = E_(V,V') [ G(2k, d) G(dim(W_V meet W_V'), d) / (G(dim W_V, d) G(dim W_V', d)) ].
```

`W_V` and `W_V'` are sums of subspaces of the blocks `Y_i`, so they meet
blockwise. Let `a, a'` be the numbers of smoothed blocks of `V, V'`, and `s`
the number of blocks smoothed in both to the same variable. The per-block
intersection dimensions are as follows.

| block `i` in `V`, `V'` | intersection dimension |
|---|---|
| kept, kept | 2 |
| exactly one smoothed | 1 |
| both smoothed to the same `v` | 1 |
| smoothed to different variables | 0 |

(In the last row, `pi(e_v) != pi(e_(v'))` because `e_v + e_(v')` is not in
`<111>`.) Hence `dim W_V = 2k - a` and
`dim(W_V meet W_V') = 2k - a - a' + s`.

For `0 <= b` and `n := 2k`, each factor of
`G(n-b,d)/G(n,d) = prod_(i<d) (2^(n-b-i) - 1)/(2^(n-i) - 1)` is at most
`2^(-b)`. For `b <= k`, each factor is at least `2^(-b)(1 - 2^(-(n-b-i)))`.
So

```text
2^(-bd) (1 - 2^(b+d-n))  <=  G(n-b, d)/G(n, d)  <=  2^(-bd),                  (5)
```

with the lower bound for `b <= k`, where `2^(b+d-n) <= 2^(d-k) < 1`. Apply the
upper bound with `b = a + a' - s` in the numerator and the lower bound with
`b = a, a'` in the denominator. Then the ratio inside the expectation is at
most `2^(sd) (1 - 2^(d-k))^(-2)`.

Blocks are independent under `P_0(.|U)`, and a block is smoothed to the same
variable in both `V` and `V'` with probability
`sum_v (beta nu_i(v))^2 = beta^2 s_i`. Hence

```text
chi^2(mu_U || u)  <=  (1 - 2^(d-k))^(-2) prod_i (1 + beta^2 s_i (2^d - 1)) - 1  <=  chi*,
```

using `s_i <= 1` and `1 + y <= e^y`. This is Theorem CL.

**Check.** The artifact computes `chi^2` exactly by enumeration. It matches
the Gaussian-binomial formula to `1e-9` in all 24 cases. The
product bound holds, and so does `TV(mu_P, u) <= (1/2) sqrt(chi*) + 2^(d-k)`,
with worst ratio `0.45`.

**Consequence.** By Cauchy--Schwarz, `TV(mu_U, u) <= (1/2) sqrt(chi^2)`.
With (4),

```text
TV(mu_P, u)  <=  (1/2) sqrt(chi*) + 2^(l-1-k)  <=  SD^cl.                     (6)
```

## Step 4: Theorem R^cl

Assume `l >= 3`, `2^(l-k) <= 1/200` and `2k >= 3`. Let `(A, B)` have value
`1 - eta`, and let `eta_U` be the rejection probability given `U`, so that
`E_U eta_U = eta` (item 4 of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`).

**Per tuple.** By Step 2, (2) and (6),

```text
delta_U := rej_T(Fbar_U)  <=  2 eta_U + SD^cl.
```

Let `g_U` be a minimiser of `g -> Pr_(Sbar unif)[Fbar_U[Sbar] != g|_Sbar]`.
Lemma 2 on `Gr(Y, l)` (`N = 2k >= 3`, `2 <= l <= N`) bounds that error by
`20 delta_U`. Put `lambda_U := g_U o pi + h*_U`.

* By Step 1, `lambda_U` satisfies every equation of `U`, for every `U`. This
  replaces OH Step 4 and gives item 1 with exceptional measure `0`.
* By (3) and (6), `tau_U <= 20 delta_U + SD^cl`, which is the bound of OH
  Step 3 with `SD*` replaced by `SD^cl`.

So `zeta_A := E_U tau_U <= 40 eta + 21 SD^cl`.

**Gluing and collection.** OH Step 5 uses only the following:

* `zeta_A`;
* `q_UV <= 2^(l-k) <= SD^cl/3`, which holds because `SD^cl >= 3 * 2^(l-k)`;
* `r = 1/(1 - 2^(l-k)) <= 200/199`;
* `2^(-(l-1)) <= 1/4`;
* the exact uniformity of `L'` in `Gr(X_V, l-1)` given `(U, V)`.

None of these involves (Q6). Its conclusion (4) of the OH route therefore
holds verbatim with `SD^cl`:

```text
Pr_(rho') [lambda_V != lambda_U|_(X_V)] <= 164 eta + 86 SD^cl,
Pr_(rho)  [lambda_V != lambda_U|_(X_V)] <= 165 eta + 87 SD^cl.
```

OH Step 6 then gives the following.

* The outer value loss is at most `165 eta + 87 SD^cl <= 300 (eta + SD^cl)`.
  Only the gluing term appears, because every `lambda_U` satisfies `U`.
* The A-side bound is `zeta_A <= 40 eta + 21 SD^cl <= 160 (eta + SD^cl)`.
* The B-side bound is
  `zeta_B <= eta + zeta_A + 164 eta + 86 SD^cl <= 210 (eta + SD^cl)`.

Corollary P goes through word for word: choose `kappa(C)` at a member with
`A(U,L) = lambda_U|_L`. The dirt is `<= zeta_A` and the disagreement is
`<= zeta_A + zeta_B <= 370 (eta + SD^cl)`. This proves Theorem R^cl.

**Corollary N^cl.** At `eta, SD^cl <= 10^(-5)` the numbers are those of OH
Corollary N: loss `<= 0.006`, dirt `<= 0.0032`, disagreement `<= 0.0074`.

## Step 5: Corollary T

Let `q >= 1`, and let `k` be admissible. Then `k >= k_A(l, q) >= k_A(l) :=
e^l (2 l ln 2 + ln(4 * 192^2))`, because
`exp(-k/e^(ql)) <= p0^2/4 = 2^(-2l)/(4 * 192^2)`.

**Monotone in `k`.** `SD^cl` is increasing in `x := k beta^2 (2^(l-1) - 1)`
and in `eps := 2^(l-1-k)`. Both decrease in `k` once `k >= 16`, in both
readings. For `eps` this is clear. For `x`, note `k beta^2 = (log log k)^2 / k`
and look at the logarithmic derivative.

* Natural reading: it is `(2/(ln k ln ln k) - 1)/k`, which is `< 0` when
  `ln k ln ln k > 2`, and in particular for `k >= 16`.
* Base-2 reading: it is `(2/(ln k ln(log_2 k)) - 1)/k`, which is also `< 0`
  for `k >= 16`.

So it suffices to take `k = k_A(l)`.

**Large `l`.** At `k = k_A(l)`, and in both readings for `l >= 66`,
`log log k_A <= log_2(2l)` and `k_A >= l e^l`. So

```text
x  <=  (log_2(2l))^2 2^(l-1) / (l e^l)  =  ((log_2(2l))^2 / (2l)) (2/e)^l,
```

which is decreasing for `l >= 66` and below `10^(-390)` at `l = 3000`.

**The computation.** The artifact evaluates `SD^cl(l, k_A(l))` in log
arithmetic for `3 <= l < 3000`, with `s_i <= 1`. It finds:

* the last failure of `SD^cl <= 10^(-5)` is at `l = 62` in the natural
  reading and at `l = 65` in the base-2 reading;
* `SD^cl(66, k_A(66)) = 9.3e-6` in the base-2 reading;
* `SD^cl(l, k_A(l))` is decreasing in `l` on `[l_0, 3000)`;
* it is decreasing in `k` on a geometric grid of 400 points above `k_A(l)`,
  for every `37`th `l` from `l_0`.

The analytic tail above covers `l >= 3000`. For the target's side conditions:

* `2^(l-k) <= 1/200` and `2k >= 3` are immediate at `k >= k_A(66) > 10^30`;
* `2^(l-1-2k) <= 1/16` is part of admissibility.

So Corollary N^cl applies at every admissible point with `l >= 66`. This is
the target with `eta_1 = 10^(-5)`, `zeta_1 = 1/128`, `l_0 = 66`, outer value
`>= 15/16` and dirt `<= 1/64`. The statement is uniform over 3LIN inputs
because nothing above depends on the input beyond the tuple structure.

## Step 6: Corollary S^cl

The route of `near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`
uses (R) only in its Step 0, which derives the hypotheses of Theorem R, and in
Step 2, which applies "Theorem R and Corollaries P, N ... with
`eta = xi = 10^(-5)`". Replace Step 0 with the following: `SD^cl >= 3 * 2^(l-k)`
gives `2^(l-k) <= 1/200`, hence `k >= l + 3` and `2k >= 3`. These are the
hypotheses of Theorem R^cl.

Step 2 then uses Theorem R^cl, Corollary P and Corollary N^cl, which have the
same three outputs:

* outer value `>= 15/16`;
* dirt `<= 1/64`;
* disagreement `<= 1/128`.

Steps 1, 3, 4 and 5 of that route use only these outputs, condition (A) and
the decoder node, so they are unchanged. So Theorem S holds wherever (A),
`l >= 3` and `SD^cl <= 10^(-5)` hold, and by Step 5 that includes every
admissible point with `l >= 66` and `q >= 1`. []
