---
rg: 2
id: untwisted-doubling-tower-nonconstant-rank-proof
kind: route
title: Averaged ramps are superadditive under doubling, Robert's dimension-two comparison supplies the containments over the square, and the sandwich gives the rank
target: untwisted-doubling-tower-has-a-nonconstant-continuous-rank
requires: []
---

Import: L. Robert, *The Cuntz semigroup of some spaces of dimension at most two*,
arXiv:0711.4396 (C. R. Math. Rep. Acad. Sci. Canada 35 (2013)). If `X` has
covering dimension at most `2` and `H^2(K; Z) = 0` (Čech) for every compact
`K ⊂ X`, then `x -> rank x(.)` is an ordered-semigroup isomorphism
`Cu(C_0(X)) -> Lsc(X, N-bar)`. In particular, for positive `P, Q` in
`C_0(X) tensor K`, `rank P(w) <= rank Q(w)` for all `w` implies `P <~ Q`.

**Step 1 (the square qualifies).** `S = [0,1]^2` has dimension `2`. A compact
`K ⊂ S ⊂ S^2` is a proper subset, so Alexander duality gives
`H^2(K; Z) ≅ H~_(-1)(S^2 \ K) = 0`. So Robert's theorem applies on `S`.

**Step 2 (the ramps).** For `u in [0,1]`, the `k`-th entry of `g_N(u)` is positive
iff `k < r_N u - 1`. The number of such `k in {1..r_N}` is
`max(0, ceil(r_N u - 2)) = R_N(u)`, which is at most `r_N - 2`. `g_N` is continuous.

**Step 3 (superadditivity).** For `u_1, u_2 in [0,1]`,
`R_N(u_1) + R_N(u_2) <= R_(N+1)((u_1 + u_2)/2) = max(0, ceil(r_N (u_1 + u_2) - 2))`.
- If both left terms are positive, `ceil(y - 2) < y - 1` gives
  `ceil(r_N u_1 - 2) + ceil(r_N u_2 - 2) < r_N(u_1 + u_2) - 2 <= ceil(r_N(u_1 + u_2) - 2)`.
  Integers strictly below a real number that is at most an integer are at most
  that integer.
- If `R_N(u_1) = 0`, the claim is `R_N(u_2) <= R_(N+1)((u_1+u_2)/2)`, true since
  `R_N(u_2) = max(0, ceil(r_N u_2 - 2))` and `u_1 >= 0`. The case `R_N(u_2) = 0`
  is symmetric.

**Step 4 (containment).** Let `psi: X_(N+1) -> S`,
`psi(x_1, x_2, y) = (F_N(x_1), F_N(x_2))`. Leaves of `X_(N+1)` are the leaves of
the two factors, so `F_(N+1) = (F_N o pi_1 + F_N o pi_2)/2`. Hence

```text
phi_N(a_N) = psi^*( g_N(u_1) ⊕ g_N(u_2) ),        a_(N+1) = psi^*( g_(N+1)((u_1 + u_2)/2) ),
```

both in `M_(r_(N+1))(C(S))`, pulled back by the unital `*`-homomorphism
`psi^*: C(S) -> C(X_(N+1))`. The fibre ranks over `S` are
`R_N(u_1) + R_N(u_2)` and `R_(N+1)((u_1+u_2)/2)`. By Step 3 and Robert's theorem,
`g_N(u_1) ⊕ g_N(u_2) <~ g_(N+1)((u_1+u_2)/2)` in `C(S) tensor K`. `*`-homomorphisms
preserve Cuntz subequivalence, so `phi_N(a_N) <~ a_(N+1)`. The images of the `a_N`
in `A^u tensor K` are therefore Cuntz-increasing.

**Step 5 (the rank).** `Cu(A^u)` has suprema of increasing sequences. Let `a` be a
positive element representing `sup_N [a_N]`. For `tau in T(A^u)`, the functional
`d_tau` on `Cu` preserves suprema of increasing sequences, so
`d_tau(a) = sup_N d_tau(a_N)`. The restriction of `tau` to `A^u_N` is
`integral tr(.) d mu_N` for a probability measure `mu_N` on `X_N`, so

```text
d_tau(a_N) = integral R_N(F_N(x)) / r_N  d mu_N(x)   in   [ tau(h) - 2/r_N, tau(h) ],
```

using `r_N F - 2 <= R_N(F) <= r_N F` on `[0,1]`. The trace of the pushforward of
`h 1_d` to stage `N` at `x` is `F_N(x)`, so `integral F_N d mu_N = tau(h)`. Letting
`N -> infinity` gives `d_tau(a) = tau(h)`.

**Step 6 (non-constant).** `tau -> tau(h)` is weak* continuous and affine. For
`x in X_1` let `x^(N)` be the diagonal point of `X_N` (every leaf at `x`, fixed
`Y`-coordinates). These points are compatible with the coordinate projections,
so the point evaluations define a trace `tau_x` with `tau_x(h) = h(x)`. If
`h(x) != h(y)`, the rank is non-constant. Square.
