---
rg: 2
id: constant-bias-selectors-need-seed-dishonest-witnesses-proof
kind: route
title: Read the selector's own bits at the witness's seed labels, bound the ev-dishonest satisfied mass by seed disagreement plus kappa, and run the honest list decoder at advantage gamma'
target: constant-bias-selectors-need-seed-dishonest-witnesses
requires:
  - efficient-branch-selectors-list-decode-honest-outer-labels
  - near-perfect-selectors-die-on-every-rigid-doubled-lec
artifacts:
  - experiments/ugc-constant-bias-2026-09-17/check_seed_dishonest_mass.py
---

Notation is that of the target.

## Step 1: Lemma F

Let `H = (sigma, tau)` be any labelling and `H0 = (sigma*, tau*)` a
`lambda`-reference with defect `r`. Split the set whose mass is `D(H, lambda)`,

```text
X := { e in Sat(H) : ev_e(sigma_(p_e)) != <lambda_(a_e), x_e> },
```

into three parts.

1. `X1 := X ∩ { tau_(q_e) != tau*_(q_e) }`. Since `X1` lies in `Sat(H)`,
   `mu(X1) <= beta(H, H0)`.
2. `X2 := X ∩ { e notin Sat(H0) or ev_e(sigma*_(p_e)) != <lambda_(a_e), x_e> }`.
   By the defect bound, `mu(X2) <= r`.
3. `X3 := X \ (X1 ∪ X2)`.

Take `e = (p, q)` in `X3`. Then:

- `pi_e(sigma_p) = tau_q`, because `e` is in `Sat(H)`;
- `tau_q = tau*_q`, because `e` is not in `X1`;
- `tau*_q = pi_e(sigma*_p)`, because `e` is in `Sat(H0)`.

So `pi_e(sigma_p) = pi_e(sigma*_p)`. Also
`ev_e(sigma*_p) = <lambda_(a_e), x_e> != ev_e(sigma_p)`, so `sigma_p != sigma*_p`.

Hence `X3` is contained in the set
`{ e : sigma_(p_e) != sigma*_(p_e), pi_e(sigma_(p_e)) = pi_e(sigma*_(p_e)) }`.
For each `p`, the pair `(sigma_p, sigma*_p)` is fixed. So the conditional mass
of that set given `p_e = p` is at most `c(p)`, and

```text
mu(X3) <= E_(p ~ mu_P) c(p) <= kappa.
```

Therefore `D(H, lambda) <= beta(H, H0) + r + kappa`.

(Checks (K), (F) and the per-vertex check (Fp) of the artifact test this on the
plain Grassmann 2-to-1 game, on random and on honest-then-corrupted labellings,
with `kappa = 1/(2^l - 1)` verified exactly.)

**Corollary C' from Lemma F.** Given (Seed), take its `lambda` and `H0`. Then
`D(H, lambda) <= (gamma - gamma' - r - kappa) + r + kappa = gamma - gamma'`,
which is (Str).

## Step 2: the selector's bits predict the linear form at the witness's seeds

Fix a YES input `x`, and condition on the event, of probability `>= theta`,
that `o := S(x)` has `val(U_o) >= 1/2 + gamma`. Let `W = (sigma_p, (tau_q, b_q))`
be a lift labelling attaining that value. Put `H := (sigma, tau)`.

Every constraint that `W` satisfies in `U_o` has `pi_e(sigma_p) = tau_q`, so it
is in `Sat(H)`. Hence `val_G(H) >= val(U_o, W) >= 1/2 + gamma`. By (Str) there
is `lambda` with `val_Phi(lambda) >= 1 - eps` and `D(H, lambda) <= gamma - gamma'`.

Let `T := { e : W satisfies e in U_o }`. For `e` in `T`, the bit-free branch
identity of `near-perfect-selectors-die-on-every-rigid-doubled-lec` gives
`G_e(tau_q, b_q) = ev_e(sigma_p)`. If also `e` is not in `X` (the ev-dishonest
satisfied set of Step 1), then `ev_e(sigma_p) = <lambda_(a_e), x_e>`, because
`T` lies in `Sat(H)`. So

```text
Pr_(e~mu) [ G_e(h_(q_e)) = <lambda_(a_e), x_e> ]
    >= mu(T) - mu(X)
    >= (1/2 + gamma) - (gamma - gamma')  =  1/2 + gamma',
```

where `h_q := (tau_q, b_q)` is a seed labelling with alphabet
`Sigma_q x {0,1}` of size `<= 2^l`.

(Checks (I) and (P) of the artifact test the identity and this inequality for
random orientations and random or partly bit-aligned lift labellings.)

## Step 3: the honest list decoder

Steps 1 to 4 of `efficient-branch-selectors-list-decode-honest-outer-labels-proof`
use the witness only through three facts:

- Step 1 inequality: a seed labelling `h` and an outer labelling `lambda` with
  `val_Phi(lambda) >= 1 - eps` satisfy
  `Pr_e[ g_e(h_(w_e)) = <lambda_(a_e), x_e> ] >= 1/2 + gamma`;
- the seed alphabet bound `|Sigma_w| <= 2^l`;
- the computability of `g_e` from the selector's output.

After that inequality they invoke only (E), (M) and (S).

Here the bit function is `g_e := G_e`. It is computable in polynomial time from
`o`, because it inverts a bijection on `2^l` labels. Step 2 supplies the
inequality with `gamma'` in place of `gamma`. So the decoder of Step 0 there
can be run with `s` uniform in `Sigma_q x {0,1}` and threshold `gamma'/2`, with
`tau <= gamma'/4`.

It then yields `E_(rho_A) q >= p/K` with `p = gamma'^3 2^(-l-2)`, and
`E val_Phi(hat lambda) >= c0 = p^2/K^2 - 2 eps`. It accepts YES inputs with
probability `>= theta c0/2`. It never accepts NO inputs, since there
`val(Phi) <= s < c0/2`. So `Lang in RP`. `square`

## Remarks

* Nothing in Steps 1 to 3 uses the views of `S`, its parity leakage, or any
  certificate. The witness `W` is existential and never computed.
* Step 2 loses nothing on constraints that `W` violates. Those are simply not
  counted, which is why a violated mass of up to `1/2 - gamma` is harmless. The
  cost of non-honesty is only the satisfied, ev-dishonest mass. That is why the
  theorem reaches every value above `1/2`, while the endpoint-agreement
  formulation of Theorem 1 (near-honest within `zeta < gamma`) and the 99%
  rigidity of Theorem S\* do not.
