---
rg: 2
id: one-compressor-liftable-masa-iff-type-orbits-tight-proof
kind: route
title: Transported holonomy eigenbases give the masa on bounded orbits, and a slow phase along long orbits is a central element no partition resolves
target: one-compressor-liftable-masa-iff-type-orbits-tight
requires: []
---

Notation of the claim; `tau` is the normalized trace and `V = V_n` at a fixed stage. Conjugation by `V`
permutes the `e_x`, so all types on one orbit have equal trace.

**0. Two identities.** For a partition `{q_A}` of `M_(N_n)`, signs `c_A` and `g = sum_A c_A q_A`:
- `||[u, g]||_2^2 = sum_(A,B) |c_A - c_B|^2 tau(q_A u q_B u^*)` for a unitary `u`. For independent uniform
  signs its mean is `sum_A ||[u, q_A]||_2^2`, and for `|c_A| <= 1` it is at most `2 sum_A ||[u, q_A]||_2^2`.
- `E ||[g, y]||_2^2 = 2 ||y - sum_A q_A y q_A||_2^2` for every `y`.

So `prod_U C_n <= {V}'` iff `eps_n^2 = sum_A ||[V_n, q_A]||_2^2 -> 0`, and `(prod_U C_n)' cap M` is the
ultraproduct of the block-diagonal algebras (choose signs attaining the mean on a `U`-large set).

## Tight periods give a masa

**1. Construction.** Fix an orbit `O = {x, beta x, ..., beta^(l-1) x}`. `V^l e_x` normalizes the factor
`A_x`, so `Ad V^l` restricts to an automorphism of `A_x`, which is inner: `Ad w_x` with `w_x` unitary in
`A_x`. Let `D_x` be the diagonal masa of `A_x` for an eigenbasis of `w_x`, and `D_(beta^k x) = V^k D_x V^(-k)`.
For each minimal projection `p` of `D_x` put `q_p = sum_(k < l) V^k p V^(-k)`.
- `V^l p V^(-l) = w_x p w_x^* = p`, so `V q_p V^* = q_p`. The `q_p` lie in `A_n`, are pairwise orthogonal,
  and sum to `1` over all orbits.
- Hence `C = prod_U span{q_p}` is abelian and lies in `Q`.

**2. The block-diagonal part of `A_n`.** Let `y in C_n' cap A_n`. Since the `e_x` are central,
`y = sum_x y_x` with `y_x in A_x`. On `e_(beta^k x)` the blocks restrict to the minimal projections of
`D_(beta^k x)`, which is maximal abelian in `A_(beta^k x)`. So `y_(beta^k x) in D_(beta^k x)`.

**3. Maximality.** Let `y in Q cap C'` with `||y|| <= 1`. By step 0 it has representatives `y_n` in
`C_n' cap M_(N_n)`, and the block-diagonal expectation keeps them in `A_n` because the blocks lie in
`A_n`. By step 2, on an orbit put `z_k = V^(-k) y_(beta^k x) V^k in D_x`.
- Because `V y_x V^*` lives on `e_(beta x)`, `||[V, y]||_2^2 = sum_x ||V y_x V^* - y_(beta x)||_2^2`. On
  `O` the terms are `||z_k - z_(k+1)||_2^2` for `k < l-1`, and `||w_x z_(l-1) w_x^* - z_0||_2^2 = ||z_(l-1) - z_0||_2^2`,
  since `z_(l-1)` commutes with `w_x in D_x`.
- `tau(q_p y) = sum_k tau(p z_k)` and `tau(q_p) = l tau(p)`. So on `O`, `E_C y` is the transport of the
  mean `zbar = (1/l) sum_k z_k in D_x`, and `||y - E_C y||_2^2` restricted to `O` is `sum_k ||z_k - zbar||_2^2`.
- The `l`-cycle has first Laplacian eigenvalue `4 sin^2(pi/l) >= 16/l^2`. So
  `sum_k ||z_k - zbar||_2^2 <= (l^2/16) sum_k ||z_k - z_(k+1)||_2^2`, cyclically.
- Summing: `||y_n - E_(C_n) y_n||_2^2 <= (K^2/16) ||[V_n, y_n]||_2^2 + 4 tau(P_(n,>K))` for every `K`.

Along `U` the first term vanishes. Tightness makes the second small for large `K`. So `y in C`, and `C`
is maximal abelian in `Q`.

## Escaping mass kills every liftable masa

**4. The escaping level.** Suppose `tau(P_(n,>K)) -> delta_K` along `U` with `delta_K` decreasing to
`delta > 0`. The sets `U_K = {n : tau(P_(n,>K)) > delta/2}` lie in `U`. Put
`K_n = max{K <= n : n in U_1 cap ... cap U_K}`. Then `K_n -> infinity` along `U`, and
`tau(P_(n,>K_n)) > delta/2` for `U`-most `n`.

**5. The central element.** Let `C = prod_U C_n <= Q` be liftable, with summed boundary `eps_n -> 0` by
step 0. Put `theta_n = (eps_n + K_n^(-1/2))^(1/2)` and `omega = exp(2 pi i theta_n)`. Choose a base
point `x_O` on each orbit and let

```text
f = sum_(l(O) > K_n)  sum_(k < l(O))  omega^k e_(beta^k x_O) .
```

- `f` is a contraction in `Z(A_n)`, with `||f||_2^2 = tau(P_(n,>K_n))`.
- `V f V^* = omega^(-1) f + rho`, where `rho` lives on the base points: `||rho||_2^2 <= 4 sum_O tau(P_O) / l(O) <= 4/K_n`.
- So `||[V, f]||_2 <= 2 pi theta_n + 2 K_n^(-1/2) -> 0`, and `f in Q`. It commutes with `A >= Q`, so `f in Z(Q)`.

**6. Block averages vanish.** Fix a block `q = q_A` and put `x = q - V q V^*`.
- `V^* f V = omega f + rho'` with `rho' = -omega V^* rho V`, so `||rho'||_2 <= 2 K_n^(-1/2)`.
- `tau(V q V^* f) = tau(q V^* f V) = omega tau(q f) + tau(q rho')`, hence
  `(1 - omega) tau(q f) = tau(x f) + tau(q rho')`.
- `x = r x r` for the projection `r = q join V q V^*`, with `tau(r) <= 2 tau(q)`. So
  `|tau(x f)| <= ||x||_1 <= sqrt(2) tau(q)^(1/2) ||[V, q]||_2`.
- `sum_A |tau(q_A rho' q_A)| <= sum_A tau(q_A)^(1/2) ||q_A rho' q_A||_2 <= ||rho'||_2`.
- With Cauchy--Schwarz, `sum_A |tau(q_A f)| <= (sqrt(2) eps_n + 2 K_n^(-1/2)) / |1 - omega|`.
- `|1 - omega| = 2 sin(pi theta_n) >= 4 theta_n` once `theta_n <= 1/2`. So
  `sum_A |tau(q_A f)| <= (eps_n + K_n^(-1/2))^(1/2) / 2 -> 0`.

**7. Conclusion.** `E_(C_n) f = sum_A (tau(q_A f)/tau(q_A)) q_A`, so
`||f - E_(C_n) f||_2^2 = ||f||_2^2 - sum_A |tau(q_A f)|^2 / tau(q_A) >= tau(P_(n,>K_n)) - sum_A |tau(q_A f)|`.
Its limit along `U` is at least `delta/2`. So `f in Z(Q)` is not in `C`. Every masa of `Q` contains `Z(Q)`,
so `C` is not maximal abelian in `Q`.

**8. Realization.** For a representation `sum_rho rho (x) C^(m_rho)` of `Gamma x|_alpha Z` with pairwise
inequivalent `rho`, `A_n = pi_n(Gamma)'` has types indexed by `rho`. The image of the generator of `Z`
normalizes `A_n` and moves `z_rho` to `z_(rho o alpha^(-1))`. With `Gamma` Kazhdan,
`at-op62-holds-for-representation-lifts` identifies `sigma(Gamma)' cap M` with `prod_U A_n`, and then
`sigma(G)' cap M = {V}' cap prod_U A_n`.
