---
rg: 2
id: projective-rank-psl-ultraproducts-embed-by-adjoint-proof
kind: route
title: Bound the rank of Ad(h) - 1 above by the image of BX - XB and below by the Jordan count of the commutant
target: projective-rank-psl-ultraproducts-embed-by-adjoint
requires: []
artifacts: [research/artifacts/fg-simple-weak-soficity-finite-field-linear-2026-09-13.md]
---

Section 1 of the artifact (Lemma 1 and Corollary 2).

1. **Upper bound.** Write `h = lambda (1 + B)` with `rk B = rho(h)`. Then
   `h X h^(-1) - X = lambda (BX - XB) h^(-1)`. As `X` varies, this lies in `(B M_n + M_n B) h^(-1)`, of dimension
   `<= 2 n rho(h)`.
2. **Lower bound.** `rk(Ad(h) - 1) = n^2 - dim C(h)`, where `C(h)` is the commutant of `h` in `M_n(F)`. Its dimension is
   unchanged over the algebraic closure.
   - With generalized eigenspaces `V_mu` of dimension `m_mu`, `C(h) <= (+) End(V_mu)`.
   - On `V_mu` the commutant has dimension `sum_j (p'_j)^2 <= k_mu m_mu`, with `k_mu = dim ker(h - mu)`.
   - So `dim C(h) <= n max_mu k_mu`.
   - For `mu in F`, `k_mu <= n - rho(h)`. For `mu notin F`, Frobenius conjugates give at least two eigenvalues with
     equal `k`, so `k_mu <= n/2`.
   - Hence `rk(Ad(h) - 1) >= n min(rho(h), n/2)`.
3. **Ultraproducts.** `Ad` is multiplicative and trivial on scalars, so it factors through `PGL_n(q) >= PSL_n(q)`. By
   item 1 a sequence is `l^pr`-null iff its image is rank-null. So the induced map is a well-defined injective
   homomorphism.
4. **Linear soficity.** Compose an embedding into `prod_U (PSL_(n_i)(q_i), l^pr)` with item 3. For a countable group,
   finite partial approximations along a sequence give an embedding indexed by `N`.
