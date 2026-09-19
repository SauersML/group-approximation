---
rg: 2
id: fpbs-normal-fibre-mass-cluster-gram-representation-proof
kind: route
title: Mass transport along fibres of a normal subgroup, then Cauchy--Schwarz or a cluster-uniform root
target: fpbs-normal-fibre-mass-cluster-gram-representation
requires: []
artifacts:
  - research/artifacts/fpbs-cluster-gram-fibre-operator-2026-09-17.md
---

Notation is as in the target. `Gamma` acts on the Cayley graph by left
multiplication, and Bernoulli percolation is invariant under this action. For
`x in Gamma` and `u in Q`, the fibre `x u~ N` depends only on `x` and `u`,
because `N` is normal. Also `g K_x(omega) = K_(gx)(g omega)`, so `a_x(u)` is
equivariant.

**Mass-transport principle.** Let `F(x,y,omega) in [0,infinity]` be measurable
with `F(gx,gy,g omega) = F(x,y,omega)`. Then

```text
E sum_y F(o,y) = E sum_x F(x,o).
```

This is the standard form for a countable group acting on itself.

**Two fibre facts.** Fix `u in Q`.

- (F1) If `y in K_x ∩ x u~ N`, then `K_y = K_x` and `yN = x u~ N`. So
  `a_y(e) = a_x(u)`, and more generally `a_y(v) = a_x(uv)`, because
  `y v~ N = x u~ v~ N`.
- (F2) `o ∈ x u~ N` if and only if `x ∈ u~^{-1} N`. For such `x`,
  `x u~ N = N` and `xN = u~^{-1}N`. So `a_x(e) = a(u^{-1})` and
  `a_x(u) = a(e)` whenever `x ∈ K_o`.

## Item 1: first-moment maximality

Assume `chi := chi^N_p = E a(e) < infinity`; otherwise there is nothing to
prove. Then `A := a(e) < infinity` a.s. Note `A >= 1`, because `o ∈ K_o ∩ N`.
Write `B = a(u)` and `Z = a(u^{-1})`.

**Step 1: `B < infinity` a.s.** Take
`F(x,y) = 1{y ∈ K_x ∩ x u~ N} 1{a_y(e) = infinity}`.

- By (F1) the out-sum at `o` is `B 1{B = infinity}`.
- The in-sum at `o` is `1{A = infinity} · #{x ∈ K_o : o ∈ x u~ N}`. This vanishes
  a.s., because each term carries the factor `1{a_o(e) = infinity}`.

So `E[B 1{B = infinity}] = 0`, which gives `P(B = infinity) = 0`. Applied to
`u^{-1}`, the same argument gives `Z < infinity` a.s.

**Step 2: symmetry.** Take `F(x,y) = 1{y ∈ K_x ∩ x u~ N}`. The out-sum is `B`. By
(F2) the in-sum is `|K_o ∩ u~^{-1}N| = Z`. So `sigma_p(u) = sigma_p(u^{-1})`.
This step needs no finiteness.

**Step 3: weighted transport.** Take

```text
F(x,y) = 1{y ∈ K_x ∩ x u~ N} · a_x(u)/a_x(e) · 1{a_x(u) < infinity, a_x(e) < infinity}.
```

- The out-sum at `o` is `B^2/A`, a.s.
- By (F2), the in-sum at `o` runs over the `Z` vertices `x ∈ K_o ∩ u~^{-1}N`.
  Each contributes `a(e)/a(u^{-1}) = A/Z`. On `{Z = 0}` there are no terms.
- So the in-sum is `A 1{Z >= 1}`, a.s.

Hence

```text
E[B^2/A] = E[A 1{Z >= 1}] <= chi.
```

**Step 4: Cauchy--Schwarz.** On `{B >= 1}`, write `B = (B/sqrt A) · sqrt A`. Then

```text
sigma_p(u)^2 = (E B)^2 <= E[B^2/A] · E[A 1{B >= 1}]
             = E[A 1{Z >= 1}] · E[A 1{B >= 1}] <= chi^2.
```

QED for item 1. No amenability, no bound on the cluster size and no sharpness
input is used.

## Item 2: Gram representation

Assume `|K_o| < infinity` a.s. Take `F(x,y) = 1{y ∈ K_x} a_y(u)/|K_x|`.

- The in-sum at `o` is `sum_{x ∈ K_o} a_o(u)/|K_o| = a(u)`.
- The out-sum is `|K_o|^{-1} sum_{y ∈ K_o} a_y(u)`. Group `y` by its fibre
  `y ∈ v~ N`: there are `a(v)` such `y`, and each has `a_y(u) = a(vu)` by (F1),
  with `x = o`.

So

```text
sigma_p(u) = E[ |K_o|^{-1} sum_v a(v) a(vu) ].                    (G)
```

For finitely supported `f`, expand `sum_v |sum_u a(vu) f(u)|^2`, which is a
finite sum since `a` has finite support. Reindex `v' = vu` in each term. By (G),
its expectation after the factor `|K_o|^{-1}` is
`sum_{u,w} conj(f(u)) f(w) sigma_p(u^{-1} w)`. QED for item 2.

**Operator form.** Put `(f*h)(y) = sum_w f(y w^{-1}) h(w)`. Combining (G) with
item 1 symmetry, and substituting `y = v w`, gives

```text
sigma_p(u w^{-1}) = E[ |K_o|^{-1} sum_y a(y u^{-1}) a(y w^{-1}) ].
```

So for finitely supported `g, h >= 0`,

```text
<g, sigma_p * h> = E[ |K_o|^{-1} <a*g, a*h> ].                     (O)
```

In operator terms, `lambda_Q(sigma_p) = E[ |K_o|^{-1} lambda_Q(a)^* lambda_Q(a) ]`
in the weak sense.

## Item 3: positive definiteness

For `p < p_c(G)`, clusters are finite, so item 2 applies. The form
`sum conj(f(u)) f(w) sigma(u^{-1}w)` is nonnegative. By the symmetry of Step 2,
the substitution `f(u) -> f(u^{-1})` turns it into the form
`sum conj(f(u)) f(w) sigma(u w^{-1})`, so both conventions agree.

At `p_c`, suppose `chi^N_(p_c) < infinity`. Each `tau_p(o,x)` is nondecreasing and
left-continuous in `p`, being a supremum of finite-volume polynomials. So
`sigma_p(u)` increases to `sigma_(p_c)(u)` by monotone convergence, and by
item 1 this limit is at most `chi^N_(p_c) < infinity`. A finite quadratic form
therefore passes to the limit and stays nonnegative. QED for item 3.

## Item 4: norm bound

Let `p < p_c`. The profile `a` is finitely supported, so `lambda_Q(a)` is bounded
with `||lambda_Q(a)|| <= ||a||_1 = |K_o|`. From (O) and Cauchy--Schwarz, for
finitely supported `g, h >= 0`,

```text
<g, sigma_p*h> <= E[ |K_o|^{-1} ||lambda_Q(a)||^2 ] ||g||_2 ||h||_2,
```

which is the upper bound. Also `E[ ||lambda_Q(a)||^2/|K_o| ] <= E|K_o| = chi_p`.

The lower bound `chi^N_p <= ||sigma_p||_Q` holds trivially: take `g = h = delta_e`
and use `sigma_p(e) = chi^N_p`. It is item 4 of the sandwich node when `N` is
infinite, and the trivial pairing otherwise.

At `p_c`, `<g, sigma_p*h>` increases to `<g, sigma_(p_c)*h>` as `p ↑ p_c`, by
monotone convergence of nonnegative terms. So `<g, sigma_(p_c)*h>` is at most
`liminf_{p ↑ p_c} E_p[ ||lambda_Q(a)||^2/|K_o| ] · ||g|| ||h||`. QED.

**Remark (at `p_c` itself).** If `theta(p_c) = 0`, item 2 holds at `p_c` directly.
The same bound then holds with `E_(p_c)` in place of the liminf. Benjamini,
Lyons, Peres and Schramm (1999) prove `theta(p_c) = 0` on nonamenable unimodular
transitive graphs. The liminf form of the theorem does not use that result.
