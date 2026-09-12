---
rg: 2
id: hs-block-gap-liftable-masa-proof
kind: route
title: Random signs identify vanishing boundary with inclusion, and the Kazhdan projection of a block-diagonal element lands in any masa
target: hs-block-gap-iff-liftable-masa-of-actor-commutant
requires:
  - vertex-rounding-reduces-ccr-to-commutant-excess
artifacts:
  - research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md
---

**Random-sign identities.** Fix a partition `{q_A}` of `M_n`. Let `u` be unitary,
`f = sum_A c_A q_A`, and let the `c_A` be independent uniform signs where signs are random.
- Since `sum_B u q_B u^* = 1`,
  `||[u,f]||_2^2 = ||u f u^* - f||_2^2 = sum_(A,B) |c_A - c_B|^2 tau(q_A u q_B u^*)`.
- **Bounded coefficients.** For `|c_A| <= 1`: `||[u,f]||_2^2 <= 2 sum_A ||[u, q_A]||_2^2`.
- **Random signs.** `E ||[u,f]||_2^2 = 2 sum_(A != B) tau(q_A u q_B u^*) = sum_A ||[u, q_A]||_2^2`,
  using `||[u,q]||_2^2 = 2 tau(q) - 2 tau(q u q u^*)`.
- **Off-diagonal mass.** For any `x`, `[f,x] = sum_(A,B) (c_A - c_B) q_A x q_B`, so
  `E ||[f,x]||_2^2 = 2 || x - sum_A q_A x q_A ||_2^2`.
- **Independent sums.** For any family `X_A`, `E || sum_A c_A X_A ||_2^2 = sum_A ||X_A||_2^2`.

**(1) Boundary.** If the summed boundary tends to `0`, every element of `C` is `(f_n)` with
`f_n = sum_A c_(n,A) q_(n,A)` and `|c| <= ||f||`. So `||[sigma_n(s), f_n]||_2 -> 0` for
`s in S`, and `C <= sigma(S)' cap M = Q`. Conversely, suppose the summed boundary for some `s`
is at least `delta` on a `U`-large set. Choose signs there with
`||[sigma_n(s), f_n]||_2^2 >= delta`. Then `(f_n) in C` does not commute with `sigma(s)`.

**(2) Commutant.** `prod_U (C_n' cap M_n) <= C'` is immediate. If `x = (x_n) in C' cap M`,
choose signs with `||[f_n, x_n]||_2^2 >= 2 ||x_n - E_n x_n||_2^2`, where `E_n` is the
block-diagonal expectation. Since `(f_n) in C` commutes with `x`, `||x_n - E_n x_n||_2 -> 0`,
and `x = (E_n x_n)`.

**Off-diagonal estimate.** Let `x` be block diagonal with `||x|| <= 1` and `u` unitary. Then
`[u, x] - sum_A [q_A u q_A, x_A] = sum_(A != B) q_B [u, x] q_A`, which has two terms.
- **First term.** `sum_(A != B) q_B u q_A x_A = sum_A (1 - q_A) u q_A x_A`. Its summands are
  orthogonal in `L^2`, since `x_(A') x_A = 0` for `A != A'`. So its norm squared is at most
  `sum_A ||(1 - q_A) u q_A||_2^2 = (1/2) sum_A ||[u, q_A]||_2^2`.
- **Second term.** The same bound holds for `sum_(A != B) x_B q_B u q_A`.
- **Conclusion.** Under the boundary condition the difference tends to `0` in 2-norm. The
  diagonal part `sum_A [q_A u q_A, x_A]` is orthogonal to the off-diagonal part.

**(3) Masa gives the gap.** Suppose (F2) fails by `epsilon` on a `U`-large set, witnessed by
self-adjoint contractions `x_n in C_n' cap M_n`. Put `x = (x_n)`, so `x in C' cap M`.
- **Limit of the left side.** By (1) and the off-diagonal estimate,
  `lim_U sum_s sum_A ||[q_A sigma_n(s) q_A, x_A]||_2^2 = sum_s ||[sigma(s), x]||_2^2`.
- **Property (T).** `Ad sigma` is a unitary representation of `G` on `L^2(M)`. Its fixed
  vectors are `L^2(Q)`, and the projection onto them restricts to `E_Q` on `M`. So
  `sum_s ||[sigma(s), x]||_2^2 >= max_s ||[sigma(s), x]||_2^2 >= kappa_S^2 ||x - E_Q(x)||_2^2`.
- **Bimodularity.** `E_Q` is `Q`-bimodular and `C <= Q`, so `x in C'` gives
  `E_Q(x) in Q cap C' = C`. Hence `E_Q(x) = E_C(x)`.
- **Right side.** `E_C = prod_U E_(C_n)` is the trace-preserving expectation onto `C`, and
  `||x_n - E_(C_n) x_n||_2^2 = sum_A ||x_A - tau_A(x_A) q_A||_2^2`.
- **Contradiction.** The limit of the left side of (F2) is at least `kappa_S^2` times the
  limit of its right side, which contradicts a failure by `epsilon`.

**(4) Gap gives a masa.** `C` is abelian, and `C <= Q` by (1). Let `y in Q cap C'` be
self-adjoint with `||y|| <= 1`.
- By (2), `y = (y_n)` with `y_n in C_n' cap M_n` self-adjoint contractions (take real parts).
- By the off-diagonal estimate, `sum_s sum_A ||[q_A sigma_n(s) q_A, y_A]||_2^2 -> sum_s ||[sigma(s), y]||_2^2 = 0`.
- (F2) gives `lim_U ||y_n - E_(C_n) y_n||_2^2 <= epsilon / kappa'^2` for every `epsilon`. So
  `y = E_C(y) in C`, and `Q cap C' = C`.

**(5) Commutation clause.** Under (H1), item 1 of
`vertex-rounding-reduces-ccr-to-commutant-excess` gives
`Q <= sigma(Gamma)' cap M = prod_U A_n`.
- **One central element per stage.** For contractions `z_n in Z(A_n)`, `g = (z_n)` lies in
  `prod_U Z(A_n)`, which commutes with `prod_U A_n` and so with `C`. By (2),
  `||z_n - E_n z_n||_2 -> 0`, uniformly over such `z_n`: otherwise pick violating `z_n` and
  get a contradiction. Moreover
  `sum_A ||[q_A, z]||_2^2 = 2 sum_(A != B) ||q_B z q_A||_2^2 = 2 ||z - E_n z||_2^2`.
  So `sup_(z in Z(A_n), ||z|| <= 1) sum_A ||[q_A, z]||_2^2 -> 0`.
- **All central projections at once.** Let `z_i` be the minimal central projections of `A_n`.
  With independent signs `epsilon_i` and `z = sum_i epsilon_i z_i`, the independent-sum identity
  gives `E sum_A ||[q_A, z]||_2^2 = sum_(A,i) ||[q_A, z_i]||_2^2`. So
  `sum_(A,i) ||[q_A, z_i]||_2^2 -> 0`.
- **Block-dependent contractions.** For `z_A = sum_i mu_(A,i) z_i` with `|mu| <= 1`,
  `[q_A, z_A] = sum_(i != i') (mu_(A,i) - mu_(A,i')) z_(i') q_A z_i`. The entries
  `z_(i') q_A z_i` are orthogonal in `L^2`, and
  `sum_i ||[q_A, z_i]||_2^2 = 2 sum_(i != i') ||z_(i') q_A z_i||_2^2`. Hence
  `||[q_A, z_A]||_2^2 <= 2 sum_i ||[q_A, z_i]||_2^2`, and summing over `A` gives
  `sum_A ||[q_A, z_A]||_2^2 <= 2 sum_(A,i) ||[q_A, z_i]||_2^2 -> 0`.
- **Aspect-ratio functions.** `F_a(zeta_A) in Z(A_n)` is a contraction for every `a`, which
  gives the last sentence.
