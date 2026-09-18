---
rg: 2
id: efficient-branch-selectors-list-decode-honest-outer-labels-proof
kind: route
title: Guess one seed label, read the selector's branch bits as a predictor of a linear form, list-decode by Parseval, and decode the outer game at random from the lists
target: efficient-branch-selectors-list-decode-honest-outer-labels
requires: []
---

The notation is that of the target claim. Throughout, `chi_alpha(x) = (-1)^<alpha, x>`
and `hat F(alpha) = E_(x~U) [F(x) chi_alpha(x)]`, where `U` is uniform on `F_2^m`.

## Step 0: the run of the decoder

Given `x`, compute `R(x)` with its run. Run `S` once to get `g`. For each
`a in A` independently:

1. Sample `e ~ mu` conditioned on `a_e = a`, and set `w := w_e`.
2. Sample `s` uniformly from `Sigma_w`.
3. For `x' in F_2^m`, compute the real number
   `F(x') := E_(e ~ mu)[ (-1)^(g_e(s)) | w_e = w, a_e = a, x_e = x' ]`.
   Set `F(x') := 0` when the condition has probability zero.
4. Compute `hat F(alpha)` for every `alpha in F_2^m`, and put
   `Lambda := { alpha : hat F(alpha) >= gamma/2 }`.
5. Output `hat lambda_a`, uniform in `Lambda`, or an arbitrary label if
   `Lambda` is empty.

For `b in B`, sample `a' ~ rho(. | b)` and output
`hat lambda_b := pi_(a'b)(hat lambda_(a'))`. Accept iff
`val_Phi(hat lambda) >= c0/2`.

`G` has polynomially many constraints and `2^m` is polynomial. So steps 1-5 are
polynomial: `F` is a finite average over constraints, and `hat F` is a
`2^m x 2^m` sum.

**Soundness of the decider.** If `x notin Lang`, every outer labelling has
value `<= s < c0/2`. So the decoder never accepts.

## Step 1: advantage profile

Let `x in Lang`. Condition on the event, of probability `>= theta`, that some
`lambda` has `val_Phi(lambda) >= 1 - eps` and `val_(G_g)(hon(lambda)) >= 1/2 + gamma`.
Fix such a `lambda`, and put `h_w := hon(lambda)_w`.

By (B), every constraint that `hon(lambda)` satisfies in `G_g` has
`g_e(h_(w_e)) = <lambda_(a_e), x_e>`. Hence

```text
Pr_(e~mu) [ g_e(h_(w_e)) = <lambda_(a_e), x_e> ] >= 1/2 + gamma.
```

Let `nu` be the law of `(w_e, a_e)`. For `(w,a)` in its support, let
`beta_(w,a) := Pr[ g_e(h_w) = <lambda_a, x_e> | w_e = w, a_e = a ] - 1/2`.
Then `E_nu beta >= gamma` and `beta <= 1/2`. Put `P := Pr_nu[beta >= gamma/2]`.
Then

```text
gamma <= E_nu beta <= P * (1/2) + (1 - P) * gamma/2 <= P/2 + gamma/2,
```

so `P >= gamma`.

## Step 2: one good pair gives a short list containing the truth

Fix `(w,a)` with `beta := beta_(w,a) >= gamma/2`, and suppose step 2 of the
decoder drew `s = h_w`. This happens with probability `1/|Sigma_w| >= 2^(-l)`.

Let `D` be the law `D_(w,a)` of `x_e`. By definition of `F`,

```text
E_(x~D) [ F(x) chi_(lambda_a)(x) ]
  = E_(e~mu)[ (-1)^(g_e(s) + <lambda_a, x_e>) | w, a ] = 2 beta.
```

`|F chi| <= 1` and `F = 0` off the support of `D`. By (E),
`sum_x |D(x) - U(x)| = 2 TV(D,U) <= 2 tau`. Therefore

```text
hat F(lambda_a) = E_U [F chi_(lambda_a)]  >=  2 beta - 2 tau  >=  gamma - gamma/2 = gamma/2,
```

using `tau <= gamma/4`. So `lambda_a in Lambda`. By Parseval,
`sum_alpha hat F(alpha)^2 = E_U F^2 <= 1`, so `|Lambda| <= 4/gamma^2`. Hence
step 5 outputs `lambda_a` with probability `>= gamma^2/4`.

(Part B of the artifact checks `hat F(sigma) >= 2 beta - 2 tau`, with equality
at `tau = 0`, and the list bound, on 300 random predictors.)

## Step 3: decoding probability

Let `q_a := Pr[hat lambda_a = lambda_a]`. The decoder draws `w` from
`nu(. | a)`. Steps 1-2 give

```text
q_a >= Pr_(w ~ nu(.|a)) [beta_(w,a) >= gamma/2] * 2^(-l) * gamma^2/4,
```

so

```text
E_(a ~ nu_A) q_a >= P * 2^(-l) gamma^2/4 >= gamma^3 2^(-l-2) = p.
```

By (M), `p <= sum_a nu_A(a) q_a <= K sum_a rho_A(a) q_a`, so
`E_(rho_A) q >= p/K`.

## Step 4: outer value

Let `lambda_b` denote the `B`-part of `lambda`. Draw `(a,b) ~ rho` and
`a' ~ rho(. | b)`. Then `(a', b)` is also `rho`-distributed. The decoded edge
`(a,b)` is satisfied whenever the following four events all hold:

* `X := {hat lambda_a = lambda_a}`;
* `Y := {hat lambda_(a') = lambda_(a')}`;
* `C := {pi_ab(lambda_a) = lambda_b}`;
* `D := {pi_(a'b)(lambda_(a')) = lambda_b}`.

In that case `pi_ab(hat lambda_a) = lambda_b = pi_(a'b)(hat lambda_(a')) = hat lambda_b`.
`C` and `D` each fail with probability `<= eps`. So

```text
E val_Phi(hat lambda) >= Pr[X and Y] - 2 eps.
```

Condition on `b`. Then `a` and `a'` are independent draws from `rho(.|b)`. The
decoder uses independent coins at distinct outer vertices, so
`Pr[X and Y | a, a', b] = q_a q_(a')` when `a != a'`. When `a = a'` it is
`q_a >= q_a^2`. By Jensen,

```text
Pr[X and Y] >= E_b [ (E_(a ~ rho(.|b)) q_a)^2 ] >= (E_(rho_A) q)^2 >= p^2/K^2.
```

So `E val_Phi(hat lambda) >= c0 = p^2/K^2 - 2 eps`. Values lie in `[0,1]`, so
`Pr[val_Phi(hat lambda) >= c0/2] >= c0/2`.

The decoder therefore accepts `x in Lang` with probability `>= theta c0/2`, and
it never accepts `x notin Lang`. Repeating `O(1/(theta c0))` times gives
`Lang in RP`. If `Lang` is NP-hard under polynomial-time reductions, then
`NP in RP`. This proves Theorem 1.

(Part C of the artifact runs this decoder exactly on 40 toy composed
instances. It uses planted outer labellings with violations, advantage profiles
and adversarial decoys on wrong seed guesses. It checks
`E_(nu_A) q >= p` and `E val >= (E_(rho_A) q)^2 - 2 eps` in every trial.)

**Near-honest witnesses.** If `A` agrees with `hon(lambda)` at both endpoints of
every constraint outside a set of mass `zeta`, then `A` and `hon(lambda)`
satisfy the same oriented constraints outside that set. So
`val(hon(lambda)) >= val(A) - zeta`.

## Theorem 2

Assume `P = NP` and (B+). By search-to-decision, a polynomial-time algorithm
finds, on YES inputs, an outer labelling `lambda` with
`val_Phi(lambda) >= 1 - eps`. In every constraint `e`, orient the block that
contains the honest seed label `h := hon(lambda)_(w_e)` so that `h` is matched to
the branch whose bit at `x_e` is `<lambda_(a_e), x_e>`. Orient the other blocks
arbitrarily. Then `g_e(h) = <lambda_(a_e), x_e>`. By (B+), every constraint that
`hon(lambda)` satisfies in `G` is then satisfied in `G_g`. Hence
`val_(G_g)(hon(lambda)) = val_G(hon(lambda))`, which is `>= 1 - eta` whenever
the composition's completeness analysis gives that bound. `square`

## Part A of the artifact

The artifact checks, exhaustively over `F_2^4` with `l = 2`, the orientation
calculus that (B+) abstracts:

* every pair of 2-dimensional subspaces meeting in a line, with all 4 per-block
  orientations and all 16 global linear labels;
* every 2-to-1 restriction `L_0 -> H`.

For these it verifies that each orientation is a bijection and that an honest
labelling satisfies the oriented constraint iff the orientation bit predicts
its value at the new direction. That is 47040 cases, with 0 failures.
