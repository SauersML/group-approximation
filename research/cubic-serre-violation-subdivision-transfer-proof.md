---
rg: 2
id: cubic-serre-violation-subdivision-transfer-proof
kind: route
title: A Schur test vector of hyperbolic cosines bounds the subdivided norm, and a Schur complement over the path blocks turns the resolvent of the subdivision into the resolvent of B at a Chebyshev polynomial
target: cubic-serre-violations-transfer-to-norm-near-3-over-sqrt2
requires: []
artifacts:
  - research/artifacts/determinant-norm-room-2026-09-16.md
---

Full proofs are in the artifact, Sections 2 and 5. Finite-group numerics are in
`experiments/determinant-norm-room-2026-09-16/`. The analytic inputs are
standard:
- the Schur test for nonnegative symmetric operators;
- Perron--Frobenius monotonicity;
- multiplicativity of the Fuglede--Kadison determinant on invertibles, and
  `det exp(X) = exp Re tau(X)`;
- `(1/2pi) Delta_z log|z - t| = delta_t`.

**1. Norm.**
- *Lower bound.* The three paths at a port contain `T_(L-1,L-1,L-1)`.
- *Upper bound.* Put `theta = log sqrt 2` and use the weight `f = 1` on ports
  and `f(m) = cosh(theta(m - L/2))/cosh(theta L/2)` inside paths.
  - At internal vertices `Mf = (3/sqrt 2) f`.
  - At ports `Mf = 3 f(1) <= 3/sqrt 2 + 3 * 2^(-(L+1)/2)`, since
    `f(1) = e^(-theta) + 2 sinh(theta)/(e^(theta L) + 1)`.

**2. Spectral transfer.** For nonreal `z`, split `r_(A_L) - z` into the port
block `-z` and the path block `X = P - z`. Let `P` be the orthogonal sum of path
adjacency matrices on `L-1` vertices, one path orbit per edge orbit.
- The path resolvent at the ends is `G_11 = -U_(L-2)/U_(L-1)` and
  `G_(1,L-1) = -1/U_(L-1)`, evaluated at `z/2`.
- Each port lies on three paths, and each path joins its two ports, so the
  Schur complement is `S = (r_B - p_L(z)) / U_(L-1)(z/2)`.
- The triangular factors have determinant `1`. Multiplicativity gives

  ```text
  integral log|x - z| d mu_(A_L)
    = (k/2) sum_j log|z - lambda_j| + integral log|t - p_L(z)| d mu_B(t),
  ```

  using `3k/2` path orbits of determinant `|U_(L-1)(z/2)|`, and `S` of size
  `k`.
- Both sides are locally integrable in `z`. Applying `(1/2pi) Delta_z` gives
  `mu_(A_L) = (k/2) sum_j delta_(lambda_j) + p_L^* mu_B`. Masses check:
  `k(3L-1)/2 = (k/2)(L-1) + kL`.

**3. Violation transfer.**
- *Formula.* Use `Q(lambda_j) = R(3(-1)^j)`, and `Q = R(t)` on all `L` roots of
  `p_L = t`.
- *Removing the Dirichlet atoms.* For `R_m = (t^2 - 9)R^m`, the Dirichlet term
  vanishes. Since `||r_B|| < 3`, `log|t^2 - 9|` is bounded on `supp mu_B`, so
  the integral is `L(c + m integral_{R!=0} log|R| d mu_B)`, which is negative
  for large `m`.

**4. Hub-cycle operator.** Use types `P_0, ..., P_(2d-1)` over each `h`.
- Hub edges join `P_a` and `P_(a+1 mod 2d)` over `h`.
- External edges join `(h, P_(2i-2))` and `(h s_i, P_(2i-1))`.

The operator is 3-regular with no diagonal coefficients. The hub cycle and
external edges join `(h, P_0)` to `(h s_i, P_0)`, so the graph is connected.
The stabilizer is `H`.

**5. Partial converse.**
- The nonzero `Q(lambda_j)` form Galois orbits, so their product is a nonzero
  integer, and the Dirichlet term is at least `0`.
- `N_Q(t) = Res_lambda(p_L(lambda) - t, Q(lambda))` lies in `Z[t]`. It equals
  the product of `Q` over the roots of `p_L = t`, and vanishes only on
  `p_L(Z(Q))`.
- With no atoms of `mu_B` there, the port term is
  `integral_{N_Q!=0} log|N_Q| d mu_B`, which is negative.

**6. Consequence.** Choose `L` with `3 * 2^(-(L+1)/2) < eps` and combine 1
and 3.
