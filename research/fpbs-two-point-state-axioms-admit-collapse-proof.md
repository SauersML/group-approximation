---
rg: 2
id: fpbs-two-point-state-axioms-admit-collapse-proof
kind: route
title: Glue a theta-squared constant onto the critical state, use Fell absorption for its spectrum and a convexity identity for Harris, and run the Riccati comparison against truncations
target: fpbs-two-point-state-axioms-admit-collapse
requires:
  - fpbs-critical-no-infinite-cluster
  - fpbs-uniqueness-spectral-atom-decomposition
  - fpbs-kazhdan-uniform-walk-decorrelation
  - fpbs-cluster-count-trichotomy
  - fpbs-bk-majorant-integrated-sensitivity-is-critical-l2
  - fpbs-acylindrically-hyperbolic-critical-l2-gap
artifacts:
  - research/artifacts/fpbs/spectral-spike.md
---

Notation is that of the target. Positive definite (PD) means
`sum_(x,y) conj(c_x) c_y g(x^(-1)y) >= 0` for finitely supported `c`. For a
PD `g` with `g(e) = 1`, let `(pi_g, H_g, xi_g)` be its GNS triple, so
`g(x) = <xi_g, pi_g(x) xi_g>`. For a symmetric probability measure `mu` we
then have `sum_x mu^(*n)(x) g(x) = <xi_g, pi_g(mu)^n xi_g>`. The quantity
called `rho` in `research/artifacts/fpbs/spectral-spike.md` is the lazy norm
`rho_L` here.

## Step 0. Three elementary facts

**(0a) Convexity lemma.** Let `t: Gamma -> [0,1]` satisfy
`t(xy) >= t(x) t(y)`, let `a in [0,1]`, and put `h = a + (1-a) t`. Then

```text
h(xy) - h(x)h(y) >= a(1-a)(1-t(x))(1-t(y)) >= 0.
```

*Proof.* Using `t(xy) >= t(x)t(y)`,

```text
h(xy) - h(x)h(y) >= a + (1-a)t(x)t(y)
                    - [a^2 + a(1-a)(t(x)+t(y)) + (1-a)^2 t(x)t(y)]
                 = a(1-a) - a(1-a)(t(x)+t(y)) + a(1-a) t(x)t(y)
                 = a(1-a)(1-t(x))(1-t(y)).  ∎
```

**(0b) Right continuity of theta.** The function `theta` is right-continuous
on `[0,1]`, and `theta(p) -> 0` as `p` decreases to `p_c`.

*Proof.* `theta(p) = inf_R P_p(e <-> ∂B_R)`. Each term is a polynomial in
`p` and nondecreasing, so `theta` is upper semicontinuous and nondecreasing,
hence right-continuous. Also `theta(p_c) = 0` by
`fpbs-critical-no-infinite-cluster`. ∎

**(0c) Right continuity of tau at p_c.** For every `x`,
`tau_p(x) -> tau_(p_c)(x)` as `p` decreases to `p_c`.

*Proof.* Let `R > |x|` and let `tau^R_p(x)` be the probability that
`e <-> x` inside `E(B_R)`. Then
`{e <-> x} ⊆ {e <-> x in E(B_R)} ∪ {e <-> ∂B_R}`, so

```text
tau_(p_c)(x) <= tau_p(x) <= tau^R_p(x) + P_p(e <-> ∂B_R).
```

Both terms on the right are polynomials. Letting `p` decrease to `p_c`, then
`R -> infinity`, and using `tau^R_(p_c) <= tau_(p_c)` and `theta(p_c) = 0`,
gives the claim. ∎

## Step 1. The critical state is a coefficient of an amplified regular representation

**Lemma 1.** `tau_(p_c)` is a coefficient of `lambda ⊗ 1` on
`l2(Gamma) ⊗ K` for some Hilbert space `K`. Consequently:

* `sum_x mu_L^(*n)(x) tau_(p_c)(x) = int_[0,rho_L] t^n d nu_(p_c)(t)`, where
  `nu_(p_c)` is a probability measure with `nu_(p_c)({1}) = 0`;
* `0 <= a_n(tau_(p_c)) <= rho^n`;
* `tau_(p_c)(x) -> 0` as `x -> infinity`.

*Proof.* At `p_c` every cluster is finite a.s.
(`fpbs-critical-no-infinite-cluster`). Let `(Omega, P)` be Bernoulli(`p_c`)
bond percolation, with `Gamma` acting by translation. Let
`H = L2(Omega; l2(Gamma))` with

```text
(pi(g)F)(omega)(y) = F(g^(-1) omega)(g^(-1) y).
```

This is `kappa ⊗ lambda`, where `kappa` is the Koopman representation. Put
`F(omega) = 1_(C_e(omega)) / |C_e(omega)|^(1/2)`, a unit vector in
`l2(Gamma)` a.s. Then `(pi(x)F)(omega) = 1_(C_x(omega)) / |C_x(omega)|^(1/2)`,
and

```text
<F, pi(x)F> = E[ sum_y 1{y in C_e} 1{y in C_x} / |C_e|^(1/2) |C_x|^(1/2) ]
            = E[ 1{e <-> x} |C_e| / |C_e| ] = tau_(p_c)(x).
```

By Fell absorption, `kappa ⊗ lambda ≅ 1_(L2(Omega)) ⊗ lambda`. So
`tau_(p_c)` is a coefficient of `lambda ⊗ 1`, whose operators `pi(mu)`
have norm `||lambda(mu)||`.

* For `mu_S`, symmetry gives `|<F, pi(mu_S)^n F>| <= rho^n`, and the value is
  nonnegative because `tau >= 0`.
* For `mu_L`, `pi(mu_L)` is positive with spectrum in `[0, rho_L]`. The
  spectral measure of `F` gives `nu_(p_c)`. Since `rho_L < 1`, `nu_(p_c)`
  has no atom at one.
* Coefficients of `lambda ⊗ 1` are limits in sup norm of finite sums of
  coefficients `<delta_a ⊗ k, (lambda(x) ⊗ 1)(delta_b ⊗ k')>`. Each of these
  vanishes off one point, so the limit is in `c_0`. ∎

## Step 2. Bernoulli satisfies (T1)–(T8) (part 1)

Let `g_p = tau_p` and `u = 1{U_p}`.

**(T1).** For finitely supported `c`,
`sum_(x,y) conj(c_x) c_y 1{x <-> y} = sum_K |sum_(x in K) c_x|^2 >= 0`,
where the sum runs over clusters `K`. Take expectations and use invariance,
`P(x <-> y) = tau_p(x^(-1)y)`. Symmetry and `tau_p(e) = 1` are immediate.

**(T2).** Use the standard coupling `omega_p = {U_e <= p}`. The events
`{e <-> x in omega_p}` and `{x <-> xy in omega_q}` are both decreasing in
the i.i.d. uniforms, so Harris' inequality applies. Since
`omega_q ⊆ omega_p`,

```text
tau_p(xy) >= P(e <-> x in omega_p, x <-> xy in omega_q)
          >= tau_p(x) P(x <-> xy in omega_q) = tau_p(x) tau_q(y).
```

**(T3), (T4).** These hold by the coupling, and by definition.

**(T5).** Step 2 of `fpbs-kazhdan-uniform-walk-decorrelation-proof` does not
use property (T). It realises `tau_p` as a coefficient of a unit vector
`xi_e` in the cluster Koopman representation, and shows that the projection
onto the invariant vectors satisfies `||Q xi_e||^2 = theta(p)^2 1{U_p}`. The
operator `pi(mu_L)` is a positive contraction. Its eigenspace for eigenvalue
one is exactly the invariant vectors, since `<pi(mu_L)v, v> = ||v||^2`
forces `pi(s)v = v` for all `s in S`. So the spectral measure of `xi_e` is
`theta^2 u delta_1 + nu_p`, where `nu_p({1}) = 0` and `nu_p` has mass
`1 - theta^2 u`.

* `u` is nondecreasing by `fpbs-cluster-count-trichotomy` (Häggström–Peres–
  Schonmann).
* When `u = 1`, `nu_p` is supported in `[0, rho_L]` by
  `fpbs-uniqueness-spectral-atom-decomposition` (Section 4 of
  `research/artifacts/fpbs/spectral-spike.md`, whose `rho` is `rho_L`).

**(T6).** This is the Theorem of `fpbs-kazhdan-uniform-walk-decorrelation`.

**(T7).** This is (0c).

**(T8).** This is (4b) and (4e) of
`fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof`, in integrated
form. The truncated `tau^R_p(e,x)` is a polynomial satisfying (4.1):

```text
d/dp tau^R_p(e,x) <= d (T^R_p P_R T^R_p)(e,x) <= d (T_p P T_p)(e,x).
```

Integrating from `q` to `p` gives
`tau^R_p(e,x) - tau^R_q(e,x) <= d int_q^p (T_s P T_s)(e,x) ds`. The
integrand is a countable sum of nonnegative functions that are nondecreasing
in `s`, hence measurable. As `R -> infinity`, `tau^R_p -> tau_p` and
`tau^R_q -> tau_q`, since both are increasing unions. So the inequality
passes to the limit. ∎

## Step 3. The witness satisfies (T1)–(T8) (part 2)

On `[0, p_c]` we have `f = tau`, and `u = 0` there as for Bernoulli, because
`theta = 0` and `U_p` fails. Every axiom that involves only parameters
`<= p_c` is therefore inherited from Step 2. Write `t = tau_(p_c)` and
`a(p) = theta(p)^2`. For every `p >= p_c`, `f_p = a(p) + (1 - a(p)) t`; at
`p = p_c` this is `t`.

**(T1).** The constant one and `t` are PD with value one at `e`, so every
convex combination is too. Symmetry and values in `[0,1]` are clear.

**(T3).** For `p_c <= q <= p`,
`f_p - f_q = (theta(p)^2 - theta(q)^2)(1 - t) >= 0`. For `q <= p_c <= p`,
`f_q = tau_q <= t <= f_p`.

**(T2).** `t` is supermultiplicative, by (T2) for Bernoulli at `q = p = p_c`.
By (0a), `f_p(xy) >= f_p(x) f_p(y)`, and by (T3), `f_p(y) >= f_q(y)` for
`q <= p`. Together these give the mixed form.

**(T4).** By definition.

**(T5).** For `p > p_c` take `u = 1`; then `u` is nondecreasing. By Lemma 1,

```text
a^L_n(f_p) = theta(p)^2 + (1 - theta(p)^2) int t^n d nu_(p_c)(t),
```

so the remainder is `(1 - theta^2) nu_(p_c)`. It has mass `1 - theta^2`, no
atom at one, and support in `[0, rho_L]`.

**(T6).** By Lemma 1, `a^L_n(f_p) <= theta^2 + (1 - theta^2) rho_L^n`.

* If `kappa > 0`, then `lambda ⊗ 1` has no nonzero invariant vectors, since
  `Gamma` is infinite.
* So, as in Step 3 of `fpbs-kazhdan-uniform-walk-decorrelation-proof`, the
  spectrum of `(lambda ⊗ 1)(mu_L)` lies in `[0, eta]`, i.e. `rho_L <= eta`.

**(T7).** `f_p - t = theta(p)^2 (1 - t) -> 0` by (0b).

**(T8).** Let `q < p`.

* If `p <= p_c`, the inequality is inherited from Step 2.
* If `p > p_c`, put `s_0 = max(q, p_c) < p`. For `s in (s_0, p]`,
  `theta(s) > 0` (definition of `p_c`) and `f_s >= theta(s)^2`. Hence

  ```text
  (F_s P F_s)(e,x) = (1/d) sum_u sum_(v ~ u) f_s(u) f_s(v^(-1) x) >= theta(s)^4 sum_u 1 = +infinity.
  ```

  The integrand is `+infinity` on a set of positive length, so the right side
  is `+infinity`.

**Conclusions for `p > p_c`.**

* `a^L_n(f_p)` decreases to `theta(p)^2 > 0`.
* `theta(p)^2 <= a_n(f_p) <= 1`, so `lambda(f_p) = 1` and
  `A(f_p) = +infinity`.
* For finite `B`,
  `<1_B, F_p 1_B> >= theta(p)^2 |B|^2 = theta(p)^2 |B| ||1_B||^2`, so
  `||F_p||_(2->2) = +infinity`.
* The lazy walk spectral measure is `theta^2 delta_1 + (1 - theta^2) nu_(p_c)`. ∎

## Step 4. No truncation system for the witness (part 3)

Assume `M = ||T_(p_c)||_(2->2) < infinity`. This holds whenever
`p_c < p_(2->2)`, since `T_p` is entrywise nondecreasing in `p`, and in
particular on every acylindrically hyperbolic Cayley graph
(`fpbs-acylindrically-hyperbolic-critical-l2-gap`).

Suppose finite kernels `tau^R_p` on `B_R` are continuously differentiable
in `p`, satisfy (4.1), increase in `R` to `f_p`, and satisfy `tau^R_(p_c) <= f_(p_c) = t`.

* Steps (4c)–(4e) of
  `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof` use only
  these four properties and `||T^R_(p_c)|| <= M`, which follows from
  `0 <= T^R_(p_c) <= T` entrywise. Differentiability of a *finite* matrix
  family is what makes the Dyson comparison in (4d) valid.
* So `f_(p_c+delta)(x) <= sum_k (d delta)^k [T(PT)^k](e,x)` for
  `0 < delta < 1/(dM)`.
* Pairing with `P^n(e,x)` gives
  `a_n(f_(p_c+delta)) <= M rho^n / (1 - d delta M) -> 0`.

This contradicts `a_n(f_(p_c+delta)) >= theta(p_c+delta)^2 > 0`. Bernoulli
has the system `tau^R_p` of (4b), and satisfies the bound, by part (2) of
`fpbs-bk-majorant-integrated-sensitivity-is-critical-l2`. ∎

## Step 5. The obstruction and its failing step

**Kill.** Suppose an argument, on some nonamenable Cayley graph, derives one
of the following from (T1)–(T8) applied to `g = tau`:

* `lim a^L_n(g_p) = 0` for some `p > p_c`;
* `lambda(g_p) < 1` for some `p > p_c`;
* `A(g_p) < infinity` for some `p > p_c`;
* `||G_p||_(2->2) < infinity` for some `p > p_c`;
* an exponential decay bound on `a_n(g_p)` for some `p > p_c`.

By part 2 the same argument applies to `g = f`, which has none of these
properties. So no such argument exists.

* The first item is nonuniqueness at `p`, by (T5) for Bernoulli.
* The second is NC, and the third is VIS.
* PB ⇒ IS ⇒ NC by `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`,
  and GB ⇒ VIS by `fpbs-green-visit-kernel-ordering`. So the class proves
  none of PB, IS, NC, GB, VIS or `p_c < p_u`.

**Semicontinuity.** Suppose `g_(p_k) -> g` pointwise with every `g_(p_k)`
PD and normalised. Then the lazy spectral measures converge weakly on
`[0,1]`: all moments are finite sums against `mu_L^(*n)` of the values, so
the moments converge.

* *Atom.* `m(h) = inf_n a^L_n(h)` is an infimum of weak*-continuous
  functionals. Its value `nu({1})` is therefore upper semicontinuous:
  `limsup m(g_(p_k)) <= m(g)`. With (T7) at `p_c` this gives only
  `theta(p)^2 u(p) -> 0` as `p` decreases to `p_c`, which is (0b).
* *Rate.* `lambda_L(h) = max supp nu_h` is lower semicontinuous under weak
  convergence, because every open set charged by the limit is eventually
  charged. `sum_n a_n` is the supremum of its partial sums. For symmetric
  `g`, `||G||_(2->2)` is the supremum of `|<psi, G psi>|` over finitely
  supported unit `psi`. Both are suprema of weak*-continuous functionals,
  hence also lower semicontinuous.
  None of the axioms bounds them from above at `p > p_c` in terms of their
  values at `p_c`.
* *(T8).* The only axiom that is not a pointwise or semicontinuity statement
  is (T8). Its integrand `G_s P G_s` is `+infinity` as soon as `theta(s) > 0`
  and `u(s) = 1`, as in Step 3. The truncations of Step 4 are what make it
  non-vacuous.

`f` realises the jumps `lambda: rho -> 1`, `A: <= 1/(1-rho) -> +infinity`
and `||.||: M -> +infinity` at `p_c`. It keeps every upper semicontinuous
invariant continuous.

## Step 6. Remarks and calibration

* *Cost.* By `fpbs-soft-collapse-iff-invariant-sparse-spines`, `F_2` carries
  no event-level soft collapse family. Part 2 still gives `f` on `F_2`.
  So any argument that uses cost must use cluster geometry, not two-point
  states.
* *Kazhdan groups.* `f` satisfies (T6), with the same uniform `eta`. On
  Kazhdan graphs, therefore, the uniform decorrelation bound together with
  the other axioms still admits collapse.
* *What is not killed.*
  * Truncation systems: Step 4 shows these separate `f` from Bernoulli
    exactly on graphs with `M < infinity`.
  * Pivotal counts in finite balls uniformly in `R`: Section 6 of the
    pivotal-kernel ordering.
  * Realisability of `g_p` as the two-point function of an invariant
    percolation with indistinguishable infinite clusters.
  * Any other event-level input.
* *Open.* On a graph with `M = infinity`, does some family satisfy (T1)–(T8)
  together with a truncation system and collapse? This is not decided here.
  Part (1) of `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2` shows
  that the Riccati comparison of Step 4 is then vacuous.
