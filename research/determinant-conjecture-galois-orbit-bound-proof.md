---
rg: 2
id: determinant-conjecture-galois-orbit-bound-proof
kind: route
title: Multiplication maps between monomial lattices of Q(zeta) give an integral model whose determinant is the index to the N times the product over the orbit
target: determinant-conjecture-bounds-determinants-over-galois-orbits
requires: []
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-one-variable-base-change-2026-09-12.md
---

The complete argument is Sections 3-4 of
`research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md`.

* **Lemma G.** `Lambda_k = span_Z {zeta^alpha : |alpha| <= k}`. The inclusion
  `Lambda_k -> Lambda_(k+1)` and multiplication by `zeta_1, zeta_2` are
  integral matrices `A_0, A_1, A_2`. Put `X_k = sum_i M_i (x) A_i`.
  - The evaluation matrices satisfy `E_(k+1) A_i = diag(sigma_j zeta_i) E_k`.
  - Then (D1)-(D3) from Lueck's Theorem 3.14, as used in the one-variable
    artifact, give
    `Delta(X_k) = [Lambda_(k+1):Lambda_k]^N prod_j Delta(M(sigma_j zeta))`.
* **Lemma H.** At each bad prime, normalize by `varpi_w` and multiply by a
  lifted norm form of `F_(q^3)/F_p`, which is unit-valued. The index
  `[O'_p : varpi^k Lambda_(k,p)]` is then eventually periodic. So the average
  index over `E` consecutive steps is `exp(h_fin)`, and `h_fin = log|c_Z|` by
  Gauss's lemma.
* **Proposition C.** `Delta(X_k) >= 1`. Add the `E` consecutive identities.
* **Corollary 6.** Combine with the min-max bound (UB2),
  `||(1,zeta) x (1,z)|| >= ||zeta - z||`, and (M3) for linear forms. Components
  inside `Y` stay at positive projective distance from `(1, z)`. `a`, `b` and
  `deg` are additive over the factorization.
