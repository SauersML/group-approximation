---
rg: 2
id: fpbs-flat-rate-point-exceeds-l2-point-on-free-products-proof
kind: route
title: Identify p_* as the Green-weighted word-sum threshold, then separate it from p_2 by strict log-convexity of the word-sum region
target: fpbs-flat-rate-point-exceeds-l2-point-on-free-products
requires: []
artifacts:
  - research/artifacts/fpbs-free-product-flat-rate-2026-09-18.md
  - experiments/fpbs-green-weighted-flat-rate-2026-09-17/certify_a_ne_b.py
  - experiments/fpbs-green-weighted-flat-rate-2026-09-17/certify_a_ne_b.out
---

The complete proof is in Sections 1–6 of the artifact. It uses:

- the normal form theorem for free products;
- the strong Markov property;
- Harris-FKG, only for existence of the limit, as in step 1 of
  `fpbs-lq-two-point-bounds-walk-rate-proof`;
- Cauchy–Schwarz;
- the identity theorem for real-analytic functions;
- one exact rational computation.

It does not use rho-transience.

1. **Generating function.** By Tonelli,
   `sum_n a_n z^n = sum_x G_z(o,x) tau_p(o,x)`. So `lambda = 1/radius`, and
   `lambda(p) = rho` iff the pairing is finite for every `z < R`.
2. **Factorization.** The prefixes of the normal form are cut vertices, and
   simple paths stay inside blocks. So `tau_p(o,x) = prod t(h_i)`, with
   `t = p` on `K_2` blocks and `t = q(p)` on `K_3` blocks, and
   `G_z(o,x) = G_z(o,o) prod f(h_i)`, with `f = a(z)` or `F(z)`.
3. **Word sums.** The fixed point `S_c* = u_c(1+S*)/(1+u_c)` bounds the
   truncated sums by induction. Conversely, a finite sum forces
   `Phi = S/(1+S) < 1`. So the sum is finite iff `Phi < 1`.
4. **`p_* = p_G`.** `a` and `F` increase strictly to `a(R)` and `F(R)`, both
   at most 1. So the pairing is finite for all `z < R` iff
   `Phi(a(R)p, 2F(R)q(p)) <= 1`.
5. **Convexity.** `D = {Phi(e^s) < 1} = {word sum < infinity}` is open and
   convex. `A` lies in `cl D`, because
   `sum_x G_z(o,x)^2 = sum_n (n+1) p^(n)(o,o) z^n < infinity` for `z < R`.
   `B` lies in `∂D` by definition of `p_2`.
6. **Strictness.** If the midpoint `M` of `A` and `B` were on `∂D`, a
   supporting line at `M` would contain `[A,B]`. Then `[A,B]` would lie in
   the graph of `h(s_2) = logit((1 - k sigma(s_2))/m)`, which is analytic and
   not affine for `(k,m) != (1,1)`. So `M` is in `D` whenever `A != B`, which
   gives `p_G > p_2`.
7. **`A != B`.** Otherwise `(p_2, q(p_2))` satisfies both first-step
   equations at one `z = R`. `certify_a_ne_b.py` encloses `p_2` in a dyadic
   interval of width `2^-80` and shows that the two resulting values of `z`
   are disjoint, in exact `Fraction` arithmetic, for all five listed
   `(k,m)`. The output is in `certify_a_ne_b.out`.
