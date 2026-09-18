---
rg: 2
id: fpbs-intrinsic-rates-log-lipschitz-in-parameter-proof
kind: route
title: Thin a shortest open path of length at most R with an independent Bernoulli(t/q) mask, then combine the cost (q/t)^R with finite susceptibility below p_c
target: fpbs-intrinsic-rates-log-lipschitz-in-parameter
requires:
  - fpbs-intrinsic-l2-rate-closed-zero-set
---

Complete written proof. No computation is used. Notation as in the claim.

**What is used from `fpbs-intrinsic-l2-rate-closed-zero-set`, and why it is
safe.** Only the following parts, whose proofs in
`fpbs-intrinsic-l2-rate-closed-zero-set-proof` do not use the unsupported
closedness sentence of its Step 2.

- **(F1)** Item 1: the limits `Lambda(t)` and `lambda_1(t)` exist, equal the
  infima over `R`, and `0 <= Lambda(t) <= lambda_1(t)`. Proof: its Step 1
  (BK splitting and Fekete).
- **(F2)** The fact (K1): `0 <= K <= K'` entrywise implies
  `||K||_(2->2) <= ||K'||_(2->2)`.
- **(F3)** Monotonicity: `a_R` and `log E_t|B^int_R(o)|` are nondecreasing in
  `t`. Proof: the second paragraph of its Step 2, by the monotone coupling.
- **(F4)** The zero sets contain `[0,p_c)` and `[0,p_(2->2))`: for `t < p_c`,
  "`E_t|B^int_R(o)| <= chi(t)`, so `lambda_1(t) = 0`", and if
  `||T_t|| < infinity` then `Lambda(t) = 0`. Proof: its Lemma 3.1 with the
  Duminil-Copin--Tassion import, and the last paragraph of its Step 3. Neither
  step uses closedness of a zero set.
- **(F5)** Item 4: a linear stretch constant `K` at `t` gives
  `Lambda(t) >= log(gr)/(2K)`. Proof: its Step 4, which uses only (F1).

## Step 1. Thinning

Fix `0 < t <= q <= 1`, `R >= 1` and vertices `u,v`. Let `omega_q` be
Bernoulli(`q`) bond percolation and `xi` an independent Bernoulli(`t/q`) bond
configuration, and put `omega' = omega_q ∩ xi`. Its edges are independent and
open with probability `q · t/q = t`, so `omega'` has the law of `omega_t`.

The event `A = {d_(omega_q)(u,v) <= R}` depends only on the edges of the finite
ball `B_R(u)`. Fix once and for all an enumeration of the finitely many simple
paths from `u` to `v` of length at most `R`. On `A` let `gamma(omega_q)` be the
first such path in the enumeration that is open in `omega_q`. It is a
measurable function of `omega_q`, and `|gamma| <= R`.

If every edge of `gamma` is open in `xi`, then `gamma` is open in `omega'`, so
`d_(omega')(u,v) <= R`. Since `xi` is independent of `omega_q`,

```text
P( d_(omega')(u,v) <= R )  >=  E[ 1_A (t/q)^|gamma(omega_q)| ]  >=  (t/q)^R P(A).
```

So `T^(R)_t(u,v) >= (t/q)^R T^(R)_q(u,v)`, which is the entrywise inequality
of item 1. Summing it over `v` gives
`E_t|B^int_R(o)| >= (t/q)^R E_q|B^int_R(o)|`. This is item 1.

## Step 2. Log-Lipschitz bound and continuity

By (F2) and Step 1, `||T^(R)_q|| <= (q/t)^R ||T^(R)_t||`, so
`a_R(q) <= a_R(t) + R log(q/t)`. Dividing by `R` and letting `R -> infinity`
with (F1) gives `Lambda(q) <= Lambda(t) + log(q/t)`. The same computation with
`log E|B^int_R(o)|` gives the bound for `lambda_1`.

Continuity. By (F3), for `0 < t <= q`,

```text
Lambda(t)  <=  Lambda(q)  <=  Lambda(t) + log(q/t).
```

Letting `q ↓ t` gives right-continuity at `t > 0`, and letting `t ↑ q` gives
left-continuity at `q > 0`. At `0`: `G` is locally finite with degree `d`, so
`p_c >= 1/(d-1) > 0`, and `Lambda = 0` on `[0,p_c)` by (F4). The same holds for
`lambda_1`. This is item 2.

## Step 3. Vanishing at `p_c` and the explicit bound

Let `q >= p_c` and `0 < t < p_c`. By (F4), `lambda_1(t) = 0`, so by Step 2
`lambda_1(q) <= log(q/t)`. Letting `t ↑ p_c` gives `lambda_1(q) <= log(q/p_c)`.
At `q = p_c` this is `lambda_1(p_c) = 0`, and `0 <= Lambda <= lambda_1` by (F1)
gives `Lambda(p_c) = 0` and `Lambda(q) <= log(q/p_c)`.

Zero sets. By (F3) and nonnegativity, `{Lambda = 0}` is an initial interval, and
by continuity (Step 2) it is closed, so it is `[0,p_Lambda]`. The same holds for
`lambda_1`. By (F4) and the case `q = p_c` above, `p_c <= p_lambda1`, and
`Lambda <= lambda_1` gives `p_lambda1 <= p_Lambda`. By (F4),
`p_(2->2) <= p_Lambda`.

Explicit bound for `Lambda`. `Lambda(p_Lambda) = 0` by closedness, so Step 2
with `t = p_Lambda` gives `Lambda(q) <= log(q/p_Lambda)` for `q >= p_Lambda`,
and `log(q/p_Lambda) <= log(q/p_(2->2))`. Below `p_Lambda` the rate is `0`.
This is item 3.

## Step 4. Stretch

Let `K` be a linear stretch constant at `t`. By (F5),
`Lambda(t) >= log(gr)/(2K) > 0`, since `gr > 1`. So `t > p_Lambda`, and by
Step 3, `log(gr)/(2K) <= log(t/p_Lambda)`, that is
`t >= p_Lambda gr^(1/(2K)) >= p_c gr^(1/(2K))`. For `t > p_c`, rearranging
`log(gr)/(2K) <= log(t/p_c)` gives `K >= log(gr)/(2 log(t/p_c))`. Taking the
infimum over `K` gives the bound for `K_*(t)`. If there is no stretch constant,
`K_*(t) = +infinity` and the bound holds trivially. This is item 4.

## Step 5. Rate transfer

If `Lambda(q) >= delta > 0`, then `q > p_Lambda`, and by Step 3
`delta <= log(q/p_Lambda)`, so `q >= p_Lambda e^delta >= p_c e^delta`. The
`lambda_1` case is identical with `p_lambda1 >= p_c`.

For (IL2), apply this with `q = p_u` and `delta = Lambda(p_u)`. For (UCS) with
constant `K` on `(p_u, p_u + epsilon)`, Step 4 gives `t >= p_c gr^(1/(2K))` for
every such `t`, hence `p_u >= p_c gr^(1/(2K))`. This is item 5. QED.

## Counterexample to the unsupported step

For `R >= 1` put `g_R(t) = min(1, max(1/R, 1 + R(t - p_c)))` on `[0,1]`. Each
`g_R` is continuous and nondecreasing. If `t < p_c`, then
`1 + R(t - p_c) < 1/R` for large `R`, so `g_R(t) = 1/R -> 0`. If `t >= p_c`,
then `g_R(t) = 1`. So `inf_R g_R = 1_[p_c,1]`. This is nondecreasing, upper
semicontinuous and right-continuous, but its zero set `[0,p_c)` is not closed.
So "infimum of continuous nondecreasing functions" alone does not give a closed
zero set. Step 1 of this proof is the extra input that does.
