---
rg: 2
id: bounded-triangle-removal-link-perturbation-proof
kind: route
title: Each vertex link loses at most t edges, and Weyl's inequality bounds the change of the normalized adjacency
target: local-spectral-expansion-survives-bounded-triangle-removal
requires: []
---

## Direct proof

**1. Links are simple random walks.** Fix a vertex `v`. With `μ_2` uniform, the
link measure `μ_(v,1)` is uniform on the edges of the link graph `X_v`. The vertex
measure `μ_(v,0)(x)` is proportional to `deg_(X_v)(x)`, the number of triangles
of `X` containing the edge `vx`.
- **The operator.** The adjacency operator of `X_v` is `P = D^(-1) W`. Here `W` is
  the 0/1 adjacency matrix of `X_v` and `D = diag(deg_(X_v))`, with every
  `deg_(X_v)(x) >= d`.
- **Symmetric form.** `P` is self-adjoint for the `μ_(v,0)` inner product.
  `D^(1/2) P D^(-1/2) = A := D^(-1/2) W D^(-1/2)` is a real symmetric matrix with
  the same spectrum. Its top eigenvalue is `1` and its second is at most `λ`.

**2. What removal does to a link.** The link of `v` in `X \ T` is `X_v` minus the
edges `xy` with `{v,x,y} ∈ T`. There are at most `t` of them. Each link vertex `x`
loses `e_x <= t` edges, so its degree stays at least `d - t >= 1`.
- **Purity.** No edge of `X \ T` lies in no triangle, so `X \ T` is pure. Every
  vertex of `X_v` is still a vertex of the new link.
- **The new operator.** The measures of `X \ T` are again uniform and descending.
  So the link operator is the simple random walk on `W' = W - E`, where `E` is a
  symmetric 0/1 matrix with at most `2t` nonzero entries.
- **Notation.** `D' = D - diag(e_x)` and `A' = D'^(-1/2) W' D'^(-1/2)`.

**3. Perturbation bound.** Let `S = D'^(-1/2) D^(1/2)`. It is diagonal with
entries `s_x = (deg(x)/(deg(x)-e_x))^(1/2)`.
- **Diagonal bound.** `e_x/deg(x) <= t/d`, so `1 <= s_x^2 <= d/(d-t)`. Put
  `s^2 = d/(d-t)`.
- **Factorization.** `A' = S (A - B) S`, with `B = D^(-1/2) E D^(-1/2)`.
- **The removed part.** The entries of `B` are at most `1/d`, and at most `2t` are
  nonzero, so `||B|| <= ||B||_F <= sqrt(2t)/d`.
- **Estimate.** `SAS - A = (S-I) A S + A (S-I)` and `||A|| = 1`, so

  ```text
  ||A' - A|| <= ||SAS - A|| + ||S B S||
             <= (s-1)s + (s-1) + s^2 ||B||
             =  (s^2 - 1) + s^2 ||B||
             <= t/(d-t) + (d/(d-t)) (sqrt(2t)/d)
             =  (t + sqrt(2t)) / (d - t).
  ```

**4. Eigenvalues.** For real symmetric matrices of the same size, each ordered
eigenvalue moves by at most the operator norm of the difference (Weyl's
inequality). `A'` still has top eigenvalue `1`, with eigenvector `D'^(1/2) 1`.
So its second eigenvalue is at most `λ + (t + sqrt(2t))/(d-t)`. This holds for
every vertex `v`, so `X \ T` is a `λ'`-local spectral expander. ∎
