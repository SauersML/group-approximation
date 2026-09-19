---
rg: 2
id: list-reference-constant-bias-decoding-loses-t-squared-proof
kind: route
title: Split the list-ev-dishonest satisfied mass into uncovered, reference-defect and partner-collision parts, run the parent's seed-guessing decoder against the seed-dependent reference, and extract one good outer labelling by averaging over the t indices
target: list-reference-constant-bias-decoding-loses-t-squared
requires:
  - constant-bias-selectors-need-seed-dishonest-witnesses
  - efficient-branch-selectors-list-decode-honest-outer-labels
  - near-perfect-selectors-die-on-every-rigid-doubled-lec
artifacts:
  - experiments/ugc-list-rerun-2026-09-17/check_list_lemma_f.py
---

Notation is that of the target. Write `j := i(q_e)` when `e` is fixed.

## Step 1: Lemma F_t

Let `X := { e in Sat(H) : ev_e(sigma_p) != <lambda^j_(a_e), x_e> }`, so
`mu(X) = D(H, Lambda)`. Split it.

1. `X1 := X ∩ {q_e uncovered}`. Then `mu(X1) <= beta(H, Lambda)`.
2. `X2 := (X \ X1) ∩ { e notin Sat(H0^j) or ev_e(sigma^j_p) != <lambda^j_(a_e), x_e> }`.
   This lies in the union over `i <= t` of the defect sets of `H0^i`, each of
   mass `<= r`. So `mu(X2) <= t r`.
3. `X3 := X \ (X1 ∪ X2)`. For `e = (p, q)` in `X3`: `q` is covered, so
   `tau_q = tau^j_q`; `e in Sat(H)` gives `pi_e(sigma_p) = tau_q`;
   `e in Sat(H0^j)` gives `tau^j_q = pi_e(sigma^j_p)`. Hence
   `pi_e(sigma_p) = pi_e(sigma^j_p)`, while
   `ev_e(sigma^j_p) = <lambda^j_(a_e), x_e> != ev_e(sigma_p)` forces
   `sigma^j_p != sigma_p`.

   Fix `p` and put `T_p := {sigma^1_p, ..., sigma^t_p}`, a set of at most `t`
   labels that does not depend on the edge. Every `e` in `X3` with `p_e = p`
   lies in `{ e : exists sigma' in T_p \ {sigma_p}, pi_e(sigma') = pi_e(sigma_p) }`,
   whose conditional mass given `p_e = p` is `<= c_t(p)`. Averaging,
   `mu(X3) <= kappa_t`.

So `D <= beta + t r + kappa_t`. The union bound over `T_p` gives
`c_t(p) <= min(1, t c(p))`, so `kappa_t <= min(1, t kappa)`.

**Grassmann value and sharpness.** At `p = L`, two distinct functionals
`sigma, sigma'` on `L` have the same restriction to a hyperplane `L'` iff
`L' = ker(sigma + sigma')`. Distinct `sigma'` give distinct kernels. So the
set of hyperplanes where some `sigma' in T \ {sigma}` collides with `sigma` has
exactly `|T \ {sigma}|` elements out of `2^l - 1`, and
`c_t(L) = min(t, 2^l - 1)/(2^l - 1)` (take `T` of `t` labels avoiding
`sigma`). For sharpness choose distinct nonzero `psi_1..psi_t` on `L`, honest
references `lambda^j` with `lambda^j|_L = sigma + psi_j` (so `r = 0` at `L`),
seed `tau_(ker psi_j) := sigma|_(ker psi_j) = lambda^j|_(ker psi_j)`, and on
every other hyperplane `L'` of `L` a seed different from `sigma|_(L')` (so
those edges are not satisfied). Then the satisfied edges at `L` are exactly the
`t` edges `(L, ker psi_j)`, all covered, and on each `x_e notin ker psi_j`
gives `psi_j(x_e) = 1`, i.e. `ev_e(sigma) != lambda^j(x_e)`. Conditional mass
`t/(2^l - 1)`. (Check (T) of the artifact verifies this exhaustively for
`(n, l) = (3,2), (4,2), (4,3)` on the first six `L`; check (LF) verifies
Lemma F_t on random, partner-type and greedy labellings with random lists of
size `1..2^(l+1)` and random covering maps.)

**Corollary C_t'.** Given (List-Seed_t), Lemma F_t gives
`D(H, Lambda) <= gamma - gamma'`, which is (List-Str_t).

## Step 2: the predictor against a seed-dependent reference

Fix a YES input and condition on `val(U_o) >= 1/2 + gamma` for `o = S(x)`,
with a lift labelling `W = (sigma_p, (tau_q, b_q))` attaining it. As in Step 2
of `constant-bias-selectors-need-seed-dishonest-witnesses-proof`,
`H := (sigma, tau)` has `val_G(H) >= 1/2 + gamma` and the satisfied set
`T` of `W` lies in `Sat(H)`. On `T`, the bit-free branch identity of
`near-perfect-selectors-die-on-every-rigid-doubled-lec` gives
`G_e(h_q) = ev_e(sigma_p)` with `h_q := (tau_q, b_q)`. Take the labellings
`lambda^i` and the map `i` of (List-Str_t), and let `X` be the set of
`e in Sat(H)` with `ev_e(sigma_p) != <lambda^(i(q_e))_(a_e), x_e>`, so
`mu(X) <= gamma - gamma'`. Off `X`, `ev_e(sigma_p) = <lambda^(i(q_e))_(a_e), x_e>`. So

```text
Pr_e[ G_e(h_(q_e)) = <lambda^(i(q_e))_(a_e), x_e> ]  >=  mu(T) - mu(X)  >=  1/2 + gamma'.
```

## Step 3: the unchanged decoder, analysed per seed

Run the decoder of `efficient-branch-selectors-list-decode-honest-outer-labels-proof`
(Step 0 there) with `g_e := G_e`, `s` uniform on `Sigma_q x {0,1}` and list
threshold `gamma'/2`. For `(w, a)` in the support of `nu`, put

```text
beta_(w,a) := Pr[ g_e(h_w) = <lambda^(i(w))_a, x_e> | w_e = w, a_e = a ] - 1/2 .
```

The reference index `i(w)` is constant on the conditioning event, because it
depends on the seed only. Step 2 gives `E_nu beta >= gamma'`, so, as in Step 1
there, `P := Pr_nu[beta >= gamma'/2] >= gamma'`. For a pair with
`beta_(w,a) >= gamma'/2`, Step 2 there applies verbatim with
`lambda_a := lambda^(i(w))_a`: when the guess is `s = h_w` (probability
`>= 2^(-l)`), `hat F(lambda^(i(w))_a) >= 2 beta - 2 tau >= gamma'/2`, the list
has at most `4/gamma'^2` elements, and the output is `lambda^(i(w))_a` with
probability `>= gamma'^2/4`.

Let `q^i_a := Pr[hat lambda_a = lambda^i_a]`. The event "output equals
`lambda^(i(w))_a`" is contained in the union over `i` of "output equals
`lambda^i_a`", so

```text
sum_(i <= t) q^i_a  >=  Pr_(w ~ nu(.|a))[ beta_(w,a) >= gamma'/2 ] 2^(-l) gamma'^2/4 ,
E_(nu_A) sum_i q^i  >=  P 2^(-l) gamma'^2/4  >=  p .
```

Choose `i*` maximising `E_(nu_A) q^i`. Then `E_(nu_A) q^(i*) >= p/t`, and by
(M), `E_(rho_A) q^(i*) >= p/(t K)`. The index `i*` is used only in the
analysis; the decoder does not know it.

## Step 4: outer value

Step 4 of the decoder proof uses only one good outer labelling and the numbers
`q_a = Pr[hat lambda_a = lambda_a]`. Apply it to `lambda^(i*)`, which has
`val_Phi >= 1 - eps`: `E val_Phi(hat lambda) >= (p/(tK))^2 - 2 eps = c_t0`, so
`Pr[val_Phi(hat lambda) >= c_t0/2] >= c_t0/2`. The decider accepts YES inputs
with probability `>= theta c_t0/2` and, by (S_t), never accepts NO inputs.
So `Lang in RP`. `square`

## Remarks

* The loss is `t^(-2)`, not `t^(-1)`, because Step 4 needs the same index at
  both endpoints `a, a'` of the two-step walk through `b`.
* Why the covering index must depend on the seed only: in the Fourier step the
  reference must be constant on each `(w, a)` class. An index depending on the
  A-vertex `p` would depend on the direction `x_e` inside the class (on
  Grassmann tests `p = (U, L)` with `L = L' + x_e`), and a mixture of linear
  forms selected by `x_e` need not correlate with any of them. This is why the
  partner collisions of Step 1 cannot be re-assigned to the A-side reference
  that `sigma_p` might itself equal, and why `kappa_t` is paid in seed form.
