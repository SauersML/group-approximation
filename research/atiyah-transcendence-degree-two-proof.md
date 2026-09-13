---
rg: 2
id: atiyah-transcendence-degree-two-proof
kind: route
title: Reduce to an integral two-variable pencil, apply the cycle inequality, and violate it with the Chow form of V(p_1, q)
target: atiyah-base-change-in-transcendence-degree-two-under-det
requires:
  - atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set
  - determinant-conjecture-bounds-determinants-over-galois-orbits
  - determinant-conjecture-excludes-liouville-atiyah-exceptions
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part3.md
---

The complete argument is Parts 1-3 of
`research/artifacts/atiyah-two-variable-base-change-2026-09-13-part*.md`.

* **Reduction (Part 1, Section 2).**
  - Suppose `A` has excess `kappa > 0` at `z`. The excess is never negative, by
    Lemma L of [[atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set]].
  - Linearization, the square-and-full completion and restriction of scalars
    give `M = M_0 + x_1 M_1 + x_2 M_2` over `Z[G]`, full, with
    `kappa_0 = dim ker M(z) >= 1`.
  - Lemma J supplies a proper closed `Y` over `Q` with `z notin Y` and `M`
    injective at algebraic points off `Y`.
* **Cycle inequality (Part 2).** By
  [[determinant-conjecture-bounds-determinants-over-galois-orbits]], every
  integral product `F` of linear forms at affine points satisfies
  `a(F) + (B-1) b(F) + C deg F >= 0`, with `B = N/kappa_0`. Here (UB2) is the
  min-max bound of Lemma 2 in the Liouville artifact
  ([[determinant-conjecture-excludes-liouville-atiyah-exceptions]]).
* **Construction (Part 3).** Fix `n = ceil(100 B^2)`, `n_2 = 4Bn + 1` and
  `gamma = 5B`.
  1. **Bivariate factor.** Minkowski gives `p`, `deg p <= n`, with
     `|p(z)| <= c H^(-n^2/4)`. A mediant over its irreducible factors, with
     small-height factors bounded below by `delta(T) > 0`, yields `p_1` with
     `-log|p_1(z)| >= (n^2/8) log H(p_1)`.
  2. **Shear.** Swap or shear so that `p_1` has a constant `x_2^d`
     coefficient.
  3. **Univariate polynomial.** `q in Z[x_1]`, with `deg q <= n_2`, height
     `exp(gamma L_1)` and `|q(z_1)| <= c H_2^(-2Bn)`.
  4. **Form and sizes.** Put
     `F = Res_(x_1)(q, u_2^d p_1(x_1, -(u_0 + u_1 x_1)/u_2))`. Hadamard gives
     `b(F) <= d L_2 + n_2 L_1 + c`. The Sylvester identity
     `F = A q + B R`, evaluated on `u = (1,z) x v`, gives
     `a(F) <= c + max((d - 1 - w_2) L_2 + n_2 L_1, d L_2 + (n_2 - 1) L_1 - g_1)`.
  5. **Contradiction.** Both branches of
     `a + (B-1) b + C deg F` are at most `c - L_1`, which is negative for
     `L_1` large. So `kappa_0 = 0`.
