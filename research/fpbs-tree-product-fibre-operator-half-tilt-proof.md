---
rg: 2
id: fpbs-tree-product-fibre-operator-half-tilt-proof
kind: route
title: Schur test with the end-height eigenfunction above, spectral evaluation of radial truncations at the top of the spectrum below, then the sandwich
target: fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility
requires:
  - fpbs-hutchcroft-nonunimodular-pc-below-pt
  - fpbs-quotient-l2-threshold-sandwich
  - fpbs-hp-relative-sharpness
  - fpbs-amenable-wq-normal-pu-is-relative-pc
  - fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu
artifacts:
  - experiments/fpbs-tree-product-fibre-tilt-2026-09-17/check_fibre_tilt.py
  - experiments/fpbs-tree-product-fibre-tilt-2026-09-17/check_fibre_tilt.out
---

Complete written proof. The script in `artifacts` only checks the identities
of Step 2 numerically, and the proof does not use it. Notation is as in the
claim. `A` is the adjacency operator of `T` on `l2(Lambda)`, and `rho = 2 sqrt(k-1)`.

## Step 0. The modular function of `Gamma_xi`

For `u in T`, the **parent** of `u` is its neighbour on the ray from `u` to
`xi`. The other `k-1` neighbours are its **children**. For vertices `u, v` of
`T`, let `h(u,v)` be the number of parent steps minus the number of child
steps along the geodesic from `u` to `v`. Then `h` is additive,
`h(u,v) + h(v,w) = h(u,w)`, and `Aut_xi(T)`-invariant. Put
`g(v) = (k-1)^(h(e,v)/2)`.

`Aut_xi(T) x H_grp` preserves the edges of the Cartesian product, so it lies in
`Aut(G)`. It is transitive because `Aut_xi(T)` is transitive on `T`. The
stabiliser of `(x_T,x_H)` is `Stab_xi(x_T) x {e}`. Hence, in the notation of
the import,

```text
Delta((x_T,x_H),(y_T,y_H)) = |Stab_xi(y_T) x_T| / |Stab_xi(x_T) y_T| = Delta_T(x_T,y_T).
```

Let `c` be a child of `u`.

- `Stab_xi(u)` fixes the ray from `u` to `xi` and permutes the `k-1` children
  of `u` transitively. So `|Stab_xi(u) c| = k-1`.
- `Stab_xi(c)` fixes the ray from `c` to `xi`, which passes through `u`. So
  `|Stab_xi(c) u| = 1`.

Therefore `Delta(c,u) = k-1`. `Delta` is a cocycle, so

```text
Delta((u,*),(v,*)) = (k-1)^(h(u,v)) = (g(v)/g(u))^2.            (0.1)
```

In particular `Delta ≠ 1`, and `Gamma_xi` is nonunimodular. With the import's
definition, `chi_(p,1/2) = sum_x tau_p(o,x) Delta(o,x)^(1/2)`. Grouping `x` by
fibres and using (0.1),

```text
chi_(p,1/2) = sum_(v in Lambda) sigma_p(v) g(v).                  (0.2)
```

## Step 1. The kernel on `l2(Q)` and its symmetries

Let `K(u,v) = sum_(y in H_grp) tau_p((u,e),(v,y))` for `u, v in Lambda`.

- **Left translation.** Translating by `(u^{-1},e) in Gamma` gives
  `K(u,v) = sigma_p(u^{-1}v)`. So `K` is the matrix of convolution by
  `sigma_p` on `l2(Q)`, and `||sigma_p||_Q = ||K||` in the sense of the
  sandwich node: the supremum of `<a, K b>` over nonnegative, finitely
  supported, unit vectors `a, b`.
- **Symmetry.** `tau_p` is symmetric, and translating by `(v,y)^{-1}` sends
  `((u,e),(v,y))` to `((v^{-1}u, y^{-1}), (e,e))`. Summing over `y` and using
  `H_grp`-translation invariance gives `K(u,v) = K(v,u)`.
- **Radiality.** Every `alpha in Aut(T)` acts on `G` by
  `(x_T,x_H) -> (alpha x_T, x_H)`, and `tau_p` is invariant under it. So
  `K(alpha u, alpha v) = K(u,v)`. `Aut(T)` is transitive on pairs at a given
  distance, so `K(u,v) = f_p(d(u,v))`. In particular `f_p` is well defined.

## Step 2. Sphere sums of `g`

Each vertex `v` has one parent, at height `h(e,v)+1`, and `k-1` children, at
height `h(e,v)-1`. So, pointwise on `Lambda`,

```text
(A g)(v) = (k-1)^((h+1)/2) + (k-1)(k-1)^((h-1)/2) = 2 sqrt(k-1) g(v) = rho g(v).    (2.1)
```

Let `A_n` be the distance-`n` operator, `A_n(u,v) = 1[d(u,v) = n]`. On a
`k`-regular tree,

- `A A_0 = A_1`;
- `A A_1 = A_2 + k I`;
- `A A_n = A_(n+1) + (k-1) A_(n-1)` for `n >= 2`.

So `A_n = P_n(A)`, where `P_0 = 1`, `P_1 = x`, `P_2 = x^2 - k` and
`P_(n+1) = x P_n - (k-1) P_(n-1)` for `n >= 2`. Each `A_n` has finite range,
so (2.1) iterates pointwise to `A_n g = P_n(rho) g`. Evaluating at `e`, where
`g(e) = 1`, gives

```text
sum_(|v| = n) g(v) = P_n(rho).                                     (2.2)
```

Solving the recursion at `x = rho`, where the characteristic roots coincide at
`sqrt(k-1)`, gives, for `n >= 1`,

```text
P_n(rho) = (k-1)^(n/2) (2 + (n-1)(k-2)/(k-1)).                     (2.3)
```

To check (2.3), note that it gives `P_1 = 2 sqrt(k-1)` and
`P_2 = 3k - 4 = rho^2 - k`. The expression `(k-1)^(n/2)(a + b n)` solves the
recursion for `n >= 2`. All terms are positive. Combining (0.2), (2.2) and
Step 1 gives the fibre-sum formula

```text
chi_(p,1/2) = f_p(0) + sum_(n>=1) f_p(n) P_n(rho).                 (2.4)
```

For `n >= 1` we have `P_n(rho) / ((n+1)(k-1)^(n/2))` in `[(k-2)/(2(k-1)), 1]`.
So `chi_(p,1/2) < infinity` iff `sum_n (n+1)(k-1)^(n/2) f_p(n) < infinity`.

## Step 3. Upper bound `||K|| <= chi_(p,1/2)` (Schur test)

We may assume `chi_(p,1/2) < infinity`. By Step 1 and (0.1), for every `u`,

```text
sum_v K(u,v) g(v)/g(u) = sum_(v,y) tau_p((u,e),(v,y)) Delta((u,e),(v,y))^(1/2) = chi_(p,1/2)((u,e)) = chi_(p,1/2).
```

The last equality holds because `chi_(p,1/2)` does not depend on the base
vertex, by the source's remark and transitivity of `Gamma_xi`. So `K g = chi g`
with `g > 0`, and `K` is symmetric. By the Schur test (AM-GM termwise), for
nonnegative unit vectors `a, b`,

```text
<a, K b> <= sum_(u,v) K(u,v) ( a(u)^2 g(v)/(2g(u)) + b(v)^2 g(u)/(2g(v)) ) = chi (||a||^2 + ||b||^2)/2 = chi.
```

## Step 4. Lower bound `||K|| >= chi_(p,1/2)`

- **Case 1: some `f_p(n)` is infinite.** Then some `K(u,v)` is infinite.
  Testing with `a = 1_u` and `b = 1_v` gives `||K|| = infinity`. By (2.4),
  `chi_(p,1/2) = infinity` too.
- **Case 2: every `f_p(n)` is finite.** For `M >= 0`, put
  `K_M = sum_(n<=M) f_p(n) A_n = F_M(A)`, where
  `F_M(x) = sum_(n<=M) f_p(n) P_n(x)`. This is a bounded self-adjoint operator
  with `0 <= K_M <= K` entrywise. So
  `||K|| >= sup_(a,b>=0) <a,K_M b> = ||K_M||`. The equality holds because
  `K_M` has nonnegative entries, so `|<a,K_M b>| <= <|a|,K_M|b|>`.

  By the spectral theorem, `||K_M|| = sup_(x in spec A) |F_M(x)|`. Since `A`
  is self-adjoint with nonnegative entries, `sup spec(A) = ||A||`. Kesten's
  theorem gives `||A|| = rho`, so `rho in spec(A)` and
  `||K_M|| >= F_M(rho)`. By (2.2),

  ```text
  F_M(rho) = sum_(n<=M) f_p(n) sum_(|v|=n) g(v) = sum_(|v|<=M) sigma_p(v) g(v),
  ```

  which increases to `chi_(p,1/2)` by (0.2) and monotone convergence.

Steps 3 and 4 prove part 1 of the claim. The threshold statement follows
because both sides are nondecreasing in `p`, together with the last line of
Step 2.

## Step 5. Part 2

By Step 0, `Gamma_xi` is transitive and nonunimodular. So
`fpbs-hutchcroft-nonunimodular-pc-below-pt` gives
`p_c(G) < p_c(G,Gamma_xi,1/2) = p_t`, and hence `chi_(p_c,1/2) < infinity`.
By part 1, `||sigma_(p_c)||_Q < infinity`.

`N` is infinite because `H_grp` is. Then `fpbs-quotient-l2-threshold-sandwich`
gives:

- part 6: `p_c(G) < p^Q_(2->2)(N;G)`, which is `p_t` by part 1, and also
  `p_c(G) < p_c(N;G)` and `p_c(G) < p_(2->2)(G)`;
- part 4: `p^Q_(2->2)(N;G) <= min{p_(2->2)(G), p_c(N;G)}`.

`E'(G,N)` asks for `p_c < p^Q_(2->2)` under the hypothesis
`p_c < p_c(N;G)`. It holds without the hypothesis. Case (i) of C1 in
`fpbs-relative-threshold-is-quotient-l2-threshold` is exactly
`||sigma_(p_c)||_Q < infinity`. The cases are disjoint, so (ii) is excluded.

For `F_2 x F_2` with generators `{a^±,b^±} ⊔ {c^±,d^±}`, the Cayley graph is
`T_4 x T_4`. Either factor can play the role of `Lambda` (`k = 4`), with the
other as `H_grp`.

## Step 6. Part 3

**(a) `p_c(N;G) = sup{p : f_p(0) < infinity}`.** Note that
`f_p(0) = E_p|K_o ∩ N|`.

- If `p < p_c(N;G)`, then `fpbs-hp-relative-sharpness`, with the subgroup
  `N`, gives `f_p(0) < infinity`.
- Suppose `p > p_c(N;G)`. The event that some cluster meets `N` in an
  infinite set is increasing. By the definition of `p_c(N;G)` recorded in
  `fpbs-amenable-wq-normal-pu-is-relative-pc`, it has probability one at some
  `p' in [p_c(N;G), p)`, and hence at `p` in the monotone coupling. `N` is
  countable, so some `y in N` has `P_p(|K_y ∩ N| = infinity) > 0`.
  Left translation by `y^{-1} in N` maps `N` to `N` and `y` to `o`, so
  `P_p(|K_o ∩ N| = infinity) > 0`, and `f_p(0) = infinity`.

**(b) The reformulation of `E`.** By part 2,
`p^Q_(2->2)(N;G) = p_t <= p_c(N;G)`. So `E(G,N)` is equivalent to
`p_c(N;G) <= p_t`, which is equivalent to `chi_(p,1/2) < infinity` for every
`p < p_c(N;G)`. For such `p`, (a) gives `f_p(0) < infinity`. By the last line
of Step 2, the condition is then equivalent to
`sum_(n>=1) n (k-1)^(n/2) f_p(n) < infinity`. Conversely, if that sum is
finite for every `p < p_c(N;G)`, then (2.4) and (a) give
`chi_(p,1/2) < infinity` there.

**(c) Amenable `H_grp`.** Here `N ≅ H_grp` is amenable.

- Part 3 of the sandwich gives `p^Q_(2->2)(N;G) = p_(2->2)(G)`.
- `fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu` gives
  `p_(2->2)(G) = p_u(G)`. `G = T x H` with `H` an infinite amenable Cayley
  graph and `k >= 3`, as that theorem requires.
- A normal subgroup is wq-normal, so
  `fpbs-amenable-wq-normal-pu-is-relative-pc` gives `p_c(N;G) = p_u(G)`.

Combining these with part 1,
`p_t = p^Q_(2->2) = p_(2->2) = p_u = p_c(N;G)`, and `E(G,N)` holds. This
recovers the equality `p_t = p_(2->2) = p_u` of Hutchcroft--Pan's Theorem 1.4
from their Theorem 1.2. It does not recover their `p_h`.

**(d) Where a counterexample must live.** By (c), `H_grp` must be
nonamenable. By (b), `E` fails iff `p_t < p_c(N;G)`, and then any
`p in (p_t, p_c(N;G))` is above `p_t`, which by part 2 is strictly above
`p_c(G)`. ∎
