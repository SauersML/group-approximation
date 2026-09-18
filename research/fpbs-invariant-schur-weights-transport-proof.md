---
rg: 2
id: fpbs-invariant-schur-weights-transport-proof
kind: route
title: Harnack compactness of normalized Schur weights, then mass transport with r+1/r>=2 against an invariant measure
target: fpbs-invariant-schur-weights-cannot-certify-critical-l2
requires: []
artifacts:
  - research/artifacts/fpbs/docs/free-product-critical-l2-2026-09-12.md
  - experiments/invariant-schur-weight-obstruction-2026-09-17/tree_schur_ratios.py
---

Notation as in the target. The proof is self-contained apart from one import.

**Import (S), sharpness.** This is the display before Proposition 2.3 in Hutchcroft,
arXiv:1804.10191. It is quoted in Section 2 of
`research/artifacts/fpbs/docs/free-product-critical-l2-2026-09-12.md`, and the
free-product proof route uses it the same way: for quasi-transitive `G`,
"`||T_p||_{1->1}<infinity` if and only if `p<p_c`", and
`||T_p||_{1->1} = chi_p` on a transitive graph. So `chi_(p_c) = infinity`.

## Step 0. Harnack bound

`G` is connected, so an open geodesic gives `tau_p(u,v) >= p^(d(u,v)) > 0`.
Take `h` in `W_C(p)` and vertices `u, v`. Then

```text
tau_p(v,u) h(u)  <=  (T_p h)(v)  <=  C h(v),     so     h(u)/h(v) <= C p^(-d(u,v)).
```

With `v = o` and then `u = o`: `p^(|v|)/C <= h(v) <= C p^(-|v|)`.

## Step 1. Compactness, action, and the operator norm

- **Compactness.** By Step 0, `W_C(p)` lies in the compact product
  `prod_v [p^|v|/C, C p^(-|v|)]`. The set is closed. Each map
  `h -> sum_(u in F) tau_p(v,u) h(u)` over a finite set `F` is continuous, so
  `{(T_p h)(v) <= C h(v)}` is the intersection over `F` of closed sets, and
  `h(o) = 1` is closed. `V` is countable, so the space is metrizable.
- **The action.** Substituting `u = g w` and using `tau_p(v, g w) = tau_p(g^(-1) v, w)`:

  ```text
  sum_u tau_p(v,u) h(g^(-1) u)  =  sum_w tau_p(g^(-1) v, w) h(w)  <=  C h(g^(-1) v).
  ```

  Dividing by `h(g^(-1) o)` gives `g.h` in `W_C(p)`. A direct computation shows
  `g.(g'.h) = (g g').h`. Each coordinate of `g.h` is a ratio of coordinates of `h`,
  with denominator at least `p^|g^(-1)o|/C`, so the action is continuous.
- **Norm `<=` inf.** This is the Schur test. If a positive `h` has `T h <= C h` and
  `T` is nonnegative and symmetric, then by Cauchy–Schwarz
  `|<f,Tg>| <= sum tau(u,v)|f(u)||g(v)|`, and this is at most
  `(sum_u |f(u)|^2 (Th)(u)/h(u))^(1/2) (sum_v |g(v)|^2 (Th)(v)/h(v))^(1/2) <= C ||f|| ||g||`.
- **Norm `>=` inf.** Suppose `lambda > ||T_p||`. Put
  `h = sum_(n>=0) lambda^(-n) T_p^n delta_o`, which converges in `l2`.
  - Every entry satisfies `h(v) >= delta_o(v) + tau_p(v,o)/lambda > 0`.
  - `T_p h = lambda (h - delta_o) <= lambda h`.
  - So `h/h(o)` lies in `W_lambda(p)`.

## Step 2. Transport bound

Let `mu` be a `Gamma`-invariant Borel probability measure on `W_C(p)`. Put
`r_h(u,v) = h(v)/h(u)`. This is continuous in `h`, and by Step 0 it is at most
`C p^(-d(u,v))`.

- **Pulling back the action.** By definition, `(g^(-1).h)(v) = h(g v)/h(g o)`.
  So `r_h(gu, gv) = r_(g^(-1).h)(u,v)`.
- **An invariant transport.** Define

  ```text
  F(u,v) = tau_p(u,v) * int r_h(u,v) d mu(h).
  ```

  Both `tau_p` and `mu` are invariant, so
  `F(gu,gv) = tau_p(u,v) int r_(g^(-1).h)(u,v) d mu(h) = F(u,v)`.
- **Mass transport on a group.** For every diagonally invariant `F >= 0` on
  `Gamma x Gamma`,

  ```text
  sum_y F(e,y) = sum_y F(y^(-1),e) = sum_x F(x,e),
  ```

  by invariance under `y^(-1)` and then the reindexing `x = y^(-1)`.
- **Out-mass.** By Tonelli,
  `sum_v F(o,v) = int (T_p h)(o)/h(o) d mu(h) <= C`.
- **In-mass.** By Tonelli and symmetry of `tau_p`,
  `sum_v F(v,o) = int sum_v tau_p(o,v) r_h(o,v)^(-1) d mu(h)`.
- **Combine.** The two masses are equal, and `r + 1/r >= 2` for `r > 0`, so

  ```text
  2C  >=  int sum_v tau_p(o,v) ( r_h(o,v) + r_h(o,v)^(-1) ) d mu(h)  >=  2 sum_v tau_p(o,v)  =  2 chi_p.
  ```

This proves item 2.

## Step 3. Critical form

- **No invariant measure.** At `p = p_c`, (S) gives `chi_(p_c) = infinity`. So by
  Step 2, no `W_C(p_c)` carries an invariant probability measure.
- **Stabilizers are not coamenable.** Suppose `h` is in `W_C(p_c)`, and `A` is a
  subgroup with `a.h = h` for every `a` in `A`. Suppose also that `A` is coamenable,
  so the `Gamma`-set `Gamma/A` has a `Gamma`-invariant mean `m`.
  - The orbit map `psi(gA) = g.h` is well defined and equivariant.
  - `f -> m(f o psi)` is a positive, unital, `Gamma`-invariant linear functional
    on `C(W_C(p_c))`.
  - By the Riesz representation theorem it is an invariant Borel probability
    measure. That is a contradiction.
- **Normal subgroups.** A normal `N` with `Gamma/N` amenable is coamenable. So is every
  subgroup containing a coamenable subgroup: push the invariant mean forward along
  `Gamma/A -> Gamma/B`. Hence `Stab_Gamma(h)` contains no such `N`.
- **Random weights.** A random weight with `Gamma`-invariant law that lies almost
  surely in `W_C(p)` pushes forward, by the equivariant normalization, to an
  invariant measure. So such a weight also gives `chi_p <= C`.

## Step 4. Amenable calibration

- If `Gamma` is amenable, every nonempty compact `Gamma`-space carries an invariant
  probability measure (Markov–Kakutani).
- So `C >= chi_p` whenever `W_C(p)` is nonempty. With Step 1 this gives
  `||T_p|| >= chi_p`.
- The constant weight lies in `W_(chi_p)(p)`, so `||T_p|| = chi_p`.

## Where the obstruction stops (the gate)

- **Hutchcroft's weight.** For a transitive nonunimodular closed subgroup
  `H <= Aut(G)`, the weight `Delta^(1/2)` is projectively `H`-fixed. The `H`-mass transport
  carries the modular factor `Delta`, so Step 2 does not apply.
- **Free products.** The Busemann weight of
  `fpbs-free-product-cayley-graphs-have-critical-l2-gap` is fixed by the
  stabilizer of an end in `Gamma`. That stabilizer is cyclic or trivial, hence
  not coamenable in a nonamenable free product, so there is no contradiction.

The script `experiments/invariant-schur-weight-obstruction-2026-09-17/tree_schur_ratios.py`
checks the three model weights on `T_3` at `p_c = 1/2`.
