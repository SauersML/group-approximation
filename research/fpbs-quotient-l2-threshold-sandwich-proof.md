---
rg: 2
id: fpbs-quotient-l2-threshold-sandwich-proof
kind: route
title: Pushforward of kernel products, Schur blocks with weak containment, and the Russo-BK comparison from an arbitrary base point order the quotient l2 threshold
target: fpbs-quotient-l2-threshold-sandwich
requires:
  - fpbs-bk-majorant-integrated-sensitivity-is-critical-l2
  - fpbs-hutchcroft-l2-gap-criterion
  - fpbs-critical-l2-implies-nonuniqueness
---

Complete written proof. No computation is used. Notation as in the claim.

**Imports.**

- `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2` (ESTABLISHED),
  through its proof route, Steps 3 and 4b-4d.
  - **Step 3, Lemma.** For a symmetric invariant kernel `K >= 0` on a group
    with `K(o,o) > 0`, `||K||_(2->2) = limsup_m (K^m(o,o))^(1/m)` in
    `[0,infinity]`. The proof uses only invariance, symmetry and finite
    truncations, so it holds verbatim on any countable group.
  - **Steps 4b-4d.** For a base parameter written `p_c`, they prove the
    entrywise bound `T^R_(p_c+delta) <= sum_k (d delta)^k T_0 (P_R T_0)^k` on
    the ball-truncated two-point matrices. The hypotheses are
    `T_0 = T^R_(p_c)`, `||T_0|| <= M` and `d delta M < 1`, with
    `p_c + delta <= 1`. No property of `p_c` is used. The truncated Russo-BK
    inequality (4.1) holds at every `p`. The comparison ODE and its positivity
    argument concern finite matrices. So the bound holds with any base point
    `p_0` in place of `p_c`, provided `||T_(p_0)|| <= M`.
- `fpbs-hutchcroft-l2-gap-criterion` (ESTABLISHED), item 1:
  "`||T_p||_(1->1) < infinity` iff `p < p_c`". Since
  `||T_p||_(1->1) = sum_x tau_p(o,x) = chi_p`, this says `chi_p < infinity`
  iff `p < p_c`.
- `fpbs-critical-l2-implies-nonuniqueness` (ESTABLISHED): `p_c < p_(2->2)`
  implies `p_c < p_u`.
- **Standard harmonic analysis.** Let `K` be an amenable normal subgroup of a
  countable group `R`. Then the quasi-regular representation `lambda_(R/K)`
  on `l2(R/K)` is weakly contained in `lambda_R`. The reasons:
  - `1_K ≺ lambda_K`, since `K` is amenable;
  - induction preserves weak containment;
  - `Ind_K^R 1_K = lambda_(R/K)` and `Ind_K^R lambda_K = lambda_R`.

  See Bekka, de la Harpe and Valette, *Kazhdan's Property (T)*, Appendix F on
  weak containment and induction, and Eymard (1972). Weak containment gives
  `||lambda_(R/K)(f)|| <= ||lambda_R(f)||` for `f in l1(R)`.

## Step 0. Conventions for nonnegative kernels

Let `R` be a countable group. For `f >= 0` on `R`, let `K_f(q,q') = f(q^(-1)q')`
and put

```text
N_R(f) = sup{ <g, K_f h> : g,h >= 0 finitely supported, ||g||_2 = ||h||_2 = 1 }  in [0,infinity].
```

In the claim, `||f||_R` means `N_R(f)`. Convolution is
`(f*g)(v) = sum_w f(w) g(w^(-1)v)`.

**(0a) Monotone limits.** If `f_n` increases pointwise to `f`, then
`N_R(f_n)` increases to `N_R(f)`. For fixed `g,h`, `<g, K_(f_n) h>` is a finite
sum of increasing limits, and a supremum of increasing limits is the limit of
the suprema.

**(0b) Sums and products.** `N_R(sum_k f_k) <= sum_k N_R(f_k)` follows from the
definition.

By Tonelli, `K_f K_g = K_(f*g)` entrywise:
`sum_u f(q^(-1)u) g(u^(-1)q') = (f*g)(q^(-1)q')`.

If `N_R(f)` and `N_R(g)` are finite, the kernels define bounded operators,
since a nonnegative kernel satisfies `|<a, K b>| <= <|a|, K|b|>`. Then for
finitely supported `a,h >= 0`,
`<a, K_(f*g) h> = <a, K_f (K_g h)> <= N_R(f) N_R(g) ||a|| ||h||`. So
`N_R(f*g) <= N_R(f) N_R(g)`, and the bound is trivial if either factor is
infinite.

**(0c) Operator reading.** When `N_R(f) < infinity`, `K_f` is the bounded
operator `h -> h * f-check` on `l2(R)`, with `f-check(q) = f(q^(-1))`.
Conjugating by the unitary `h -> h(.^(-1))` turns it into `lambda_R(f)`. So
`N_R(f) = ||lambda_R(f)||`, and `S_p` has norm `N_Q(sigma^N_p)`.

**(0d) Symmetry of `sigma`.** By left invariance and symmetry of connection,
`tau_p(o,x) = tau_p(x^(-1),o) = tau_p(o,x^(-1))`. As `x` runs over
`pi^(-1)(q)`, `x^(-1)` runs over `pi^(-1)(q^(-1))`. So
`sigma^N_p(q^(-1)) = sigma^N_p(q)`.

**(0e) Pushforward of products.** Let `k_1, k_2 >= 0` on `Gamma`, with
`K_i(x,y) = k_i(x^(-1)y)`. For `q in Q`, Tonelli gives

```text
sum_(y in q) (K_1 K_2)(o,y) = sum_(z in Gamma) k_1(z) sum_(y in q) k_2(z^(-1) y)
                            = sum_z k_1(z) (pi_* k_2)(pi(z)^(-1) q)
                            = ((pi_* k_1) * (pi_* k_2))(q),
```

where `(pi_* k)(q) = sum_(x in q) k(x)`. The middle step holds because, as `y`
runs over `pi^(-1)(q)`, `z^(-1)y` runs over `pi^(-1)(pi(z)^(-1)q)`.

By induction, the pushforward of a finite kernel product is the convolution
product of the pushforwards. `T_p` pushes to `sigma^N_p`. The walk kernel `P`,
with `P(x,y) = 1/d` for `x^(-1)y in S`, pushes to
`mu_Q = pi_*(uniform on S)`. In particular

```text
sigma_p^(*m)(e) = sum_(y in N) (T_p^m)(o,y) = chi^(N,m)_p.
```

## Step 1. Diagonal formula (part 1)

Apply the imported Lemma on `R = Q` to `K = K_(sigma)` with `sigma = sigma^N_p`.

- `K` is invariant.
- `K` is symmetric by (0d): `K(q',q) = sigma(q'^(-1)q) = sigma(q^(-1)q') = K(q,q')`.
- `K(e,e) = sigma(e) >= tau_p(o,o) = 1`.

By (0b), `K^m = K_(sigma^(*m))`, and `K^m(e,e) = sigma^(*m)(e) = chi^(N,m)_p`
by (0e). Hence `N_Q(sigma^N_p) = limsup_m (chi^(N,m)_p)^(1/m)`. ∎

## Step 2. Monotonicity and amenable extensions (part 2)

Let `N <= M` be normal in `Gamma`. Put `Q = Gamma/N`, `R = Gamma/M`,
`K = M/N` (normal in `Q`) and `rho: Q -> R`. By definition,
`sigma^M_p = rho_* sigma^N_p`. Write `f = sigma^N_p`, which is symmetric by (0d).

**(2a) Schur test on blocks: `N_Q(f) <= N_R(rho_* f)`.** Take finitely
supported `g,h >= 0` on `Q`. Put `G(r) = ||g 1_(rho^(-1) r)||_2` and similarly
`H(r)`. For cosets `r, r'` let `B_(r,r')` be the block of `K_f` with rows in
`rho^(-1)(r)` and columns in `rho^(-1)(r')`.

- **Row sums.** For `q in rho^(-1)(r)`,
  `sum_(q' in rho^(-1) r') f(q^(-1)q') = (rho_* f)(r^(-1)r')`, as in (0e).
- **Column sums.** For `q' in rho^(-1)(r')`,
  `sum_(q in rho^(-1) r) f(q^(-1)q') = sum_q f(q'^(-1)q) = (rho_* f)(r'^(-1)r) = (rho_* f)(r^(-1)r')`,
  using the symmetry of `f` and of `rho_* f`.

Schur's test on the block gives
`<g 1_(rho^(-1)r), B_(r,r') h 1_(rho^(-1)r')> <= (rho_* f)(r^(-1)r') G(r) H(r')`.
Summing over `(r,r')` gives `<g, K_f h> <= <G, K_(rho_* f) H>`, and `G`, `H`
are finitely supported with the same `l2` norms as `g`, `h`.

**(2b) Equality for amenable `K`.** Let `f_n = f 1_(B_n)`, where `B_n` is the
ball of radius `n` in `Q` for the word metric from `pi(S)`. Each `f_n` is
symmetric and finitely supported. The operator `lambda_(Q/K)(f_n)` on
`l2(Q/K) = l2(R)` is convolution by `rho_* f_n`, so
`||lambda_R(rho_* f_n)|| = ||lambda_(Q/K)(f_n)|| <= ||lambda_Q(f_n)||` by weak
containment. By (0c) this reads `N_R(rho_* f_n) <= N_Q(f_n)`.

As `n -> infinity`, `f_n` increases to `f` and `rho_* f_n` increases to
`rho_* f`. So (0a) gives `N_R(rho_* f) <= N_Q(f)`. With (2a) the two norms are
equal for every `p`, and so are the thresholds. ∎

## Step 3. Extremes (part 3)

**`N = {e}`.** Then `Q = Gamma` and `sigma^({e})_p = tau_p(o,.)`, so
`K_sigma = T_p` and `N_Gamma(sigma) = ||T_p||_(2->2)`. The threshold is
`p_(2->2)(G)`.

**`N = Gamma`.** Then `Q` is trivial, `sigma^Gamma_p = chi_p` and
`N_Q(sigma) = chi_p`. By the imported item 1, `chi_p < infinity` iff `p < p_c`,
so the threshold is `p_c(G)`.

**Every normal `N`.** Step 2 applies to `{e} <= N` and to `N <= Gamma`:

```text
||T_p||_(2->2)  <=  N_Q(sigma^N_p)  <=  chi_p      for every p.
```

The right inequality gives a finite norm for `p < p_c`, so
`p_c <= p^Q_(2->2)(N;G)`. The left inequality gives `||T_p|| < infinity`
wherever `N_Q(sigma^N_p) < infinity`. So `p^Q_(2->2)(N;G) <= p_(2->2)(G)`.

**Amenable `N`.** Step 2 with `{e} <= N` and `N/{e} = N` amenable turns the left
inequality into an equality, so `p^Q_(2->2)(N;G) = p_(2->2)(G)`.

**Amenable `Q`.** Step 2 with `N <= Gamma` and `Gamma/N = Q` amenable turns the
right inequality into an equality, so `p^Q_(2->2)(N;G) = p_c(G)`. ∎

## Step 4. Below the relative threshold (part 4)

**The inequality.**
`chi^N_p = sigma(e) = <delta_e, K_sigma delta_e> <= N_Q(sigma^N_p)`.

**Finite `chi^N_p` gives `p <= p_c(N;G)`.** Suppose `chi^N_p < infinity`.

1. For `x in N`, left invariance and `xN = N` give
   `E_p|K_x ∩ N| = E_p|K_o ∩ x^(-1)N| = chi^N_p`.
2. So almost surely `K_x ∩ N` is finite for every `x in N`, a countable
   intersection of full-measure events.
3. A cluster meeting `N` contains some `x in N`. Hence almost surely no cluster
   meets `N` in infinitely many vertices.
4. The existence of such a cluster is an increasing event. So `p <= p_c(N;G)`.

**The threshold bound.** Every `p` with `N_Q(sigma^N_p) < infinity` has
`chi^N_p < infinity`, hence `p <= p_c(N;G)`. Taking the supremum gives
`p^Q_(2->2)(N;G) <= p_c(N;G)`. ∎

## Step 5. Openness (part 5)

Assume `N_Q(sigma^N_(p_0)) = M < infinity`, with `p_0 + delta <= 1` and
`d delta M < 1`.

**(5a) Base-point comparison.** By Step 3, `||T_(p_0)|| <= M`. The ball-truncated
matrix `T^R_(p_0)` is entrywise below `T_(p_0)`, and a nonnegative kernel lying
below another has no larger norm. So `||T^R_(p_0)|| <= M`. The imported Steps
4b-4d, with base point `p_0`, give entrywise on `B_R x B_R`

```text
T^R_(p_0+delta) <= sum_k (d delta)^k T^R_(p_0) (P_R T^R_(p_0))^k
                <= sum_k (d delta)^k T_(p_0) (P T_(p_0))^k.
```

**(5b) Removing the truncation.** As `R -> infinity`, `tau^R_p(o,x)` increases to
`tau_p(o,x)`, because `{o <-> x}` is the increasing union of the events
`{o <-> x in E_R}`. So for all `x`,

```text
tau_(p_0+delta)(o,x) <= sum_k (d delta)^k [T_(p_0) (P T_(p_0))^k](o,x).
```

**(5c) Pushing to the quotient.** Sum over `x in q` and apply (0e) termwise
(Tonelli). Pointwise on `Q`,

```text
sigma^N_(p_0+delta) <= sum_k (d delta)^k sigma_(p_0) * (mu_Q * sigma_(p_0))^(*k).
```

A pointwise bound between nonnegative functions bounds `N_Q`. Schur's test
gives `N_Q(mu_Q) <= 1`, since `mu_Q` is a probability measure. By (0b),

```text
N_Q(sigma^N_(p_0+delta)) <= sum_k (d delta)^k M^(k+1) = M/(1 - d delta M).
```

**(5d) Consequences.** Put `p* = p^Q_(2->2)(N;G)`.

- **Lower bound.** Let `p < p*` and `M = N_Q(sigma^N_p)`.
  1. `M` is finite: the norm is nondecreasing in `p`, and some `p'` with
     `p < p' <= p*` has a finite norm.
  2. By (5c), the norm is finite at `p + delta` for every `delta < 1/(dM)`
     with `p + delta <= 1`.
  3. Hence `p* >= min{p + 1/(dM), 1}`.
  4. If `p* < 1`, this reads `p* >= p + 1/(dM)`, that is,
     `M >= 1/(d(p* - p))`.
- **Blow-up at the threshold.**
  - **If `p* < 1`.** A finite norm at `p*` would give, by (5c), a finite norm
    slightly above `p*`, contradicting the definition of `p*`.
  - **If `p* = 1` and `Gamma` is infinite.** Here `sigma^N_1(q) = |pi^(-1)(q)|`.
    - If `N` is infinite, `sigma^N_1` is identically infinite.
    - If `N` is finite, `Q` is infinite and `sigma^N_1 = |N| >= 1` is
      constant. Then `h = 1_F |F|^(-1/2)` gives `<h, K h> = |N||F| -> infinity`.

  In both cases `N_Q(sigma^N_1) = infinity`. ∎

## Step 6. Critical form (part 6)

Here `Gamma` is infinite.

- **Forward.** If `p_c < p*`, some `p > p_c` has a finite norm, and the norm at
  `p_c` is no larger.
- **Converse.** Suppose `N_Q(sigma^N_(p_c)) = M < infinity`. By the last
  bullet of (5d), the norm at `p = 1` is infinite, so `p_c < 1`. Then (5c)
  with `delta = min{1/(2dM), 1 - p_c} > 0` gives a finite norm at
  `p_c + delta > p_c`. So `p_c < p*`.
- **Consequences.** If `N` is infinite, Step 4 gives `p_c < p* <= p_c(N;G)`.
  Step 3 gives `p_c < p* <= p_(2->2)(G)`, and the imported
  `fpbs-critical-l2-implies-nonuniqueness` then gives `p_c < p_u`. ∎
