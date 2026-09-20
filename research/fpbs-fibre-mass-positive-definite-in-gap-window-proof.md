---
rg: 2
id: fpbs-fibre-mass-positive-definite-in-gap-window-proof
kind: route
title: A coset mass transport moves the fibre count from one end of a connection to the other, a probability weight on the quotient replaces the missing 1/|K| root, and the square root of a bounded positive convolution gives the regular vector
target: fpbs-fibre-mass-positive-definite-in-gap-window
requires:
  - fpbs-hp-relative-sharpness
  - fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility
artifacts:
  - experiments/fpbs-window-positive-definite-2026-09-17/check_gram_identity.py
  - experiments/fpbs-window-positive-definite-2026-09-17/check_gram_identity.out
---

Complete written proof. Notation is as in the claim. All sums of
nonnegative terms are exchanged by Tonelli. `N` is normal, so `vN = Nv` for
every `v`, and for `C ⊆ Gamma`, `g in Gamma`,

```text
A_(gC)(v) = |gC ∩ vN| = |C ∩ g^(-1) v N| = A_C(g^(-1) v),                  (0.1)
```

where `g^(-1) v` is the coset of `g^(-1) y_v`. For `n in N`,
`n^(-1) v N = v (v^(-1) n^(-1) v) N = vN`, so `A_(nC) = A_C`: every `A_C(v)`,
every `W_pi(C)`, `|C|` and `1{|C| = infinity}` are invariant under left
translation by `N`.

## Step 0. Finiteness

`chi^N_p < infinity` is the hypothesis. For `p < p_c(N;G)` it is the last
sentence of `fpbs-hp-relative-sharpness` (Hutchcroft--Pan, arXiv:2409.12283v1,
Theorem 1.8), applied with `H = N`.

By (0.1) and invariance, `E A_(K_(y_r))(r) = E A_(K_o)(e) = chi^N_p`. So almost
surely, for every `r` (countably many), the cluster of `y_r` meets `rN`
finitely often. A cluster that meets `rN` at some `x` has the same count as
`K_x`, and `x` ranges over a countable set. So almost surely every cluster
meets every fibre finitely often.

## Step 1. Translation and coset transport

**(T) Translation.** By (0.1) and invariance of the law under `y_u^(-1)`,
`E[A_(K_(y_u))(w) psi(K_(y_u))] = E[A_(K_o)(u^(-1) w) psi(K_o)] = sigma_(p,psi)(u^(-1) w)`
for every `N`-invariant `psi >= 0`.

**(C) Coset transport.** Let `psi >= 0` be `N`-invariant and put
`m(x,y) = E[1{x <-> y} psi(K_x)]`. On `{x <-> y}` we have `K_x = K_y`. Since
the law and `psi` are `N`-invariant, `m(nx,ny) = m(x,y)` for `n in N`. For
cosets `u, v`, write `vN = N y_v` and `y = n y_v`:

```text
sum_(y in vN) m(y_u, y) = sum_(n in N) m(y_u, n y_v) = sum_(n in N) m(n^(-1) y_u, y_v) = sum_(x in uN) m(x, y_v),
```

because `n^(-1) y_u` runs over `N y_u = uN`. The left side is
`E[A_(K_(y_u))(v) psi(K_(y_u))]`, and the right side is
`E[A_(K_(y_v))(u) psi(K_(y_v))]`. So

```text
E[A_(K_(y_u))(v) psi(K_(y_u))] = E[A_(K_(y_v))(u) psi(K_(y_v))].           (1.1)
```

## Step 2. Part 1 (maximality)

Symmetry: `x in q^(-1) N` iff `x^(-1) in N q = qN`, and
`tau_p(o,x) = tau_p(o,x^(-1))`. So `sigma_p(q^(-1)) = sigma_p(q)`.

Write `A = A_(K_o)`. Since `o in N`, `A(e) >= 1`. Apply (1.1) with `u = e`,
`y_e = o`, `v = q` and `psi(C) = A_C(q)/A_C(e)` on `{A_C(e) > 0}`, and
`psi = 0` otherwise. This `psi` is `N`-invariant.

```text
E[A(q)^2 / A(e)] = E[A_(K_(y_q))(e) A_(K_(y_q))(q) / A_(K_(y_q))(e); A_(K_(y_q))(e) > 0]
                 = E[A_(K_(y_q))(q); K_(y_q) meets N]  <=  E A_(K_(y_q))(q) = sigma_p(e),
```

where the last equality is (T). By Cauchy--Schwarz,

```text
sigma_p(q) = E[ (A(q)/A(e)^(1/2)) A(e)^(1/2) ] <= (E[A(q)^2/A(e)])^(1/2) (E A(e))^(1/2) <= sigma_p(e).
```

## Step 3. Part 2 (the Gram identity)

Fix `v`. The cluster `K_(y_v)` contains `y_v`, so `W_pi(K_(y_v)) >= pi_v > 0`.
By (T) and part 1,

```text
E W_pi(K_(y_v)) = sum_r pi_r sigma_p(v^(-1) r) <= sigma_p(e) < infinity,
```

so `W_pi(K_(y_v)) < infinity` almost surely. Hence for every `N`-invariant
`psi >= 0` and every `w`, the functional
`psi_w(C) = A_C(w) psi(C) / W_pi(C)` is `N`-invariant, nonnegative and finite
almost surely along `K_(y_r)` for every `r`. Apply (1.1) to `psi_w` with the pair `(v,u)`:

```text
E[A_(K_(y_v))(u) A_(K_(y_v))(w) psi(K_(y_v)) / W_pi(K_(y_v))] = E[A_(K_(y_u))(v) A_(K_(y_u))(w) psi(K_(y_u)) / W_pi(K_(y_u))].
```

Multiply by `pi_v` and sum over `v`. On the right,
`sum_v pi_v A_(K_(y_u))(v) = W_pi(K_(y_u))`, which is finite and positive
almost surely, so the ratio is `1` and the right side becomes
`E[A_(K_(y_u))(w) psi(K_(y_u))] = sigma_(p,psi)(u^(-1) w)` by (T). This is
part 2.

*Check with `N` trivial.* Then `A_C(v) = 1{v in C}`, `W_pi(C) = pi(C)`, and
the right side is `E[1{u <-> w} psi(K_u) sum_(v in K_u) pi_v / pi(K_u)]`,
which equals `P(u <-> w)` for `psi = 1`, as it must. The naive root
normalised by `A(e)` alone gives `E[A(u) A(w)/A(e)]`, which for `N` trivial is
the three-point function `P(o <-> u <-> w)`. It is wrong, and the script
confirms that it fails in every case tested (check (X)).

## Step 4. Part 3 (positive definiteness)

Let `c` be finitely supported on `Q`. Each summand below is integrable,
because `A(u) A(w)/W_pi <= A(w)/pi_u` on `K_(y_v)` whenever `A(u) > 0`. By
part 2,

```text
sum_(u,w) conj(c_u) c_w sigma_(p,psi)(u^(-1) w) = sum_v pi_v E[ |sum_w c_w A_(K_(y_v))(w)|^2 psi(K_(y_v)) / W_pi(K_(y_v)) ] >= 0.
```

The indicators `1{|C| < infinity}` and `1{|C| = infinity}` are
`N`-invariant, and they sum to `1`. So `sigma_p`, `sigma^fin_p` and
`sigma^inf_p` are positive definite, and `sigma_p = sigma^fin_p + sigma^inf_p`.

**Why the weight cannot be invariant.** The root in part 2 is the family of
vectors `u -> (pi_v / W_pi)^(1/2) A_(K_(y_v))(u)` indexed by `v`. By (0.1)
it is `Q`-equivariant only if `pi` is translation invariant, that is, the
counting measure. That choice gives `W(C) = |C|`, which is infinite on every
infinite cluster. This is where the probability weight is needed, and it is
also why part 3 does not give part 4 for `sigma^inf_p`.

## Step 5. Part 4 (finite part)

On `{|K_x| < infinity}`, `sum_(z in K_x) 1/|K_x| = 1`. So

```text
P(x <-> y, |K_x| < infinity) = sum_(z in Gamma) E[ 1{z <-> x} 1{z <-> y} 1{|K_z| < infinity} / |K_z| ].
```

Sum over `y in wN` with `x = y_u`, and group `z` by its coset `v`:

```text
sigma^fin_p(u^(-1) w) = sum_v sum_(z in vN) E[ 1{z <-> y_u} phi_w(K_z) ],     phi_w(C) = A_C(w) 1{|C| < infinity} / |C|.
```

`phi_w` is `N`-invariant. Step 1 (C) gives
`sum_(z in vN) m(z, y_u) = sum_(x in uN) m(y_v, x)`, so the inner sum is
`E[A_(K_(y_v))(u) phi_w(K_(y_v))]`. Translate by `y_v^(-1)` using (0.1), with
`a = A_(K_o)` and `F = 1{|K_o| < infinity}/|K_o|`:

```text
sigma^fin_p(u^(-1) w) = sum_v E[ a(v^(-1) u) a(v^(-1) w) F ].
```

Put `xi(x, omega) = a(x) F^(1/2)` for `x in Q`. Substituting `x = v^(-1) u`,
which runs over `Q` as `v` does, gives `v^(-1) w = x u^(-1) w`, and turns the
sum over `v` into `sum_x xi(x) xi(x u^(-1) w)`. So

```text
sigma^fin_p(q) = E sum_x xi(x) xi(xq) = <xi, (rho ⊗ 1)(q) xi>,   (rho(q) f)(x) = f(xq).
```

At `q = e`, `||xi||^2 = sigma^fin_p(e) <= chi^N_p < infinity`. So `xi` lies
in `l2(Q) ⊗ L2(Omega)`, and `sigma^fin_p` is a diagonal coefficient of a
multiple of the right regular representation. That puts it in `A(Q)`.

## Step 6. Part 5 (what Claim E forces)

Suppose `||sigma_p||_Q < infinity`. Since `0 <= sigma^inf_p <= sigma_p`
pointwise and the norm of the sandwich node is a supremum over nonnegative
vectors, `||sigma^inf_p||_Q <= ||sigma_p||_Q < infinity`. Let `L` be the
bounded operator `(L c)(u) = sum_w sigma^inf_p(u^(-1) w) c(w)`.

- By part 3, `<c, L c> >= 0` on finitely supported `c`, hence on `l2(Q)`, so
  `L >= 0`.
- `L` commutes with the left translations `(lambda(g)c)(u) = c(g^(-1)u)`,
  hence so does `L^(1/2)`.

Put `eta = L^(1/2) delta_e`. Then, with `delta_u = lambda(u) delta_e`,

```text
sigma^inf_p(u^(-1) w) = <delta_u, L delta_w> = <lambda(u) eta, lambda(w) eta> = <eta, lambda(u^(-1) w) eta>.
```

Put `xi_inf(x) = eta(x^(-1))`. Substituting `x = y^(-1)` gives
`<eta, lambda(q) eta> = <xi_inf, rho(q) xi_inf>`, and
`||xi_inf||^2 = <delta_e, L delta_e> = sigma^inf_p(e)`. This is part 5.

## Step 7. Part 6 (tree products)

Imports from the route of
`fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility`
(`fpbs-tree-product-fibre-operator-half-tilt-proof`), for the `k`-regular
tree `T = Cay(Lambda, S_Lambda)` with `rho_T = 2 sqrt(k-1)`:

- *Step 1 (radiality).* Every `alpha in Aut(T)` acts on `G` by
  `(x_T,x_H) -> (alpha x_T, x_H)` and preserves the law. It also preserves
  `|K|`. So `sigma^fin_p` and `sigma^inf_p`, like `sigma_p`, depend only on
  the tree distance.
- *Step 2, (2.1) to (2.3).* With `g(v) = (k-1)^(h(e,v)/2) > 0` and `A_n` the
  distance-`n` operator on `l2(Lambda)`, `A_n g = P_n(rho_T) g` pointwise,
  and for `n >= 1`, `P_n(rho_T) = (k-1)^(n/2) (2 + (n-1)(k-2)/(k-1))`.

`A_n` is symmetric with nonnegative entries and has the positive
eigenfunction `g`. By the Schur test (AM-GM termwise, exactly as in Step 3 of
that route), `||A_n|| <= P_n(rho_T)`.

In the Cayley graph, `d(x,y) = |x^(-1) y|`, so
`sum_(|q| = n) (rho(q) f)(x) = sum_(d(x,y) = n) f(y) = (A_n f)(x)`. With
`xi` from Step 5,

```text
|S_n| f^fin_p(n) = sum_(|q| = n) sigma^fin_p(q) = <xi, (A_n ⊗ 1) xi> <= P_n(rho_T) f^fin_p(0).
```

Here `|S_n| = k (k-1)^(n-1)`, and
`P_n(rho_T)/|S_n| = (k-1)^(-n/2) (1 + n(k-2)/k)`. For `n = 0` the bound is an
equality. The same computation applies to any diagonal coefficient
`<xi', (rho ⊗ 1)(q) xi'>`, which gives the E1 and Claim E statements. ∎

## Remark R. Positivity is not inherited from the two-point function

Let `N` be nonamenable with finite symmetric generating set `S_N`, let
`r_N = ||lambda_N(mu_(S_N))|| < 1`, and let `Gamma = N x Z/2` and
`1 < t <= 1/r_N`. Define `tau(n,0) = delta_e(n)` and
`tau(n,1) = t mu_(S_N)(n)`. Then `tau >= 0`. It is positive definite on
`Gamma`, because for `c = (c_0,c_1)` the form is

```text
||c_0||^2 + ||c_1||^2 + 2 t Re <c_0, lambda_N(mu_(S_N)) c_1>  >=  ||c_0||^2 + ||c_1||^2 - 2 t r_N ||c_0|| ||c_1||  >=  0.
```

Its fibre sums over `N` on `Q = Z/2` are `1` and `t > 1`. So the pushforward
is neither maximal at `e` nor positive definite. Parts 1 and 3 therefore use
the cluster structure (Step 1 (C)), not only positive definiteness of
`tau_p`. On finite groups the pushforward of a positive definite function is
always positive definite, so the enumeration script tests the identity of
part 2, not the conclusion of part 3.
