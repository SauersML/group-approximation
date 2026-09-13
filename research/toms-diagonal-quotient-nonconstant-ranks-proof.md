---
rg: 2
id: toms-diagonal-quotient-nonconstant-ranks-proof
kind: route
title: Dyadic leaf thresholds converge in norm to a uniformly distributed element, which is independent of central scalars on the diagonal
target: toms-diagonal-quotient-has-nonconstant-continuous-ranks
requires: []
---

Imports from arXiv:2606.12188v2, read on 2026-09-12: the Section 4 construction
(`X_(L+1)`, `gamma_(L,r) = pi_(CP)^* xi_(L,r)`, `phi_L`, `q_(L+1) = phi_L(q_L)`,
`rank p_L = rank q_L = d_L`); Lemma 2 (diagonal point traces); the Section 2
identity `Delta_n(c(F - E)) = c_(n^2)(F tensor E^*)` for equal rank `n`; and
`p_1 = theta^d`, `q_1 = S` on `Gr(d,2d)`.

**Step 1: the element `b`.**
- `q_L` is an orthogonal sum of leaf projections `1_l`, `l in {0,1}^(L-1)`, and
  `phi_L(1_l) = 1_(l0) + 1_(l1)`. Each `1_l` has fibre rank `d` inside `q_L` of
  rank `2^(L-1) d`. So its normalized trace is `1/N`, `N = 2^(L-1)`, at every
  point, hence for every trace on `A_L`.
- Put `k_l = 1 + (binary value of l)` and `b_L = sum_l (k_l/N) 1_l in A_L`. Then
  `k_(l0) = 2k_l - 1` and `k_(l1) = 2k_l`.
- On `1_(l1)` the elements `b_(L+1)` and `phi_L(b_L)` agree. On `1_(l0)` they
  differ by `1/(2N)`. So `||b_(L+1) - phi_L(b_L)|| = 2^(-L)`. The sequence is
  norm Cauchy in `A`, with limit `b` and `0 <= b <= 1`.
- For continuous `g`, `tau(g(b_L)) = (1/N) sum_(k=1..N) g(k/N)`, which tends to
  `integral_0^1 g`. So the law of `b` is Lebesgue measure for every `tau`.

**Step 2: the quotient.**
- `pi_1(x, x, l) = pi_2(x, x, l) = x`. So `phi_L(a)` restricted to `D_(L+1)`
  equals `a(x) tensor gamma_(L,1)(l) + a(x) tensor gamma_(L,2)(l)`, which depends
  only on the restriction of `a` to `D_L`.
- Restriction therefore maps the ideal of stage elements vanishing on `D_L` into
  the ideal vanishing on `D_(L+1)`. The limit of the restrictions is a surjection
  `pi: A -> A_D`.
- Toms's Lemma 2 extends a point `x in X_1` by `x_(r+1) = (x_r, x_r, l_r)`. These
  points lie in `D_(r+1)`, so `tau_x` factors through `A_D`.

**Step 3: independence and the rank.**
- On `D_L = X_1 x prod_(r<L) CP^(j_r)` every leaf coordinate equals `y in X_1`.
  So the image of `h in C(X_1) subset A_1` is `h(y)` times the unit, a central
  element commuting with `pi(b)`.
- Let `tau in T(A_D)`, with stage measure `mu_L` on `D_L`. For continuous `f` and
  `g`, the element `f(h) 1_l` is `f(h(y))` times a projection of fibre trace
  `1/N`. So

  ```text
  tau(g(b_L) f(h)) = sum_l g(k_l/N) (1/N) integral f(h(y)) d mu_L = ((1/N) sum_k g(k/N)) tau(f(h)).
  ```

  In the limit the joint law of `(pi(b), pi(h))` under `tau` is
  `Lebesgue x nu`, where `nu` is the law of `h`.
- Hence `d_tau((b - (1-h))_+)` is the product measure of `{(s,t) : s > 1 - t}`,
  which is `integral t d nu(t) = tau(h)`. This is continuous and affine in `tau`.
  It is non-constant, because `tau_y(h) = h(y)`.

**Step 4: the pair on the diagonal.**
- On `D_2 = X_1 x CP^(j_1)`, `p_2 = theta^d tensor gamma_1 + theta^d tensor gamma_2`
  and `q_2 = S tensor gamma_1 + S tensor gamma_2`. Both halves sit over the same
  `y`.
- For a d-plane `P`, let `T_P(y): C^d = P -> S_y` be orthogonal projection. It
  vanishes exactly when `S_y = P^perp`.
- For `P != P'`, the map `T = T_P tensor 1 + T_(P') tensor 1` vanishes only where
  `S_y = P^perp = P'^perp`, which is impossible. So `T` vanishes nowhere.
- For `L >= 2`, `Hom(p_L, q_L)` restricted to `D_L` contains the `N` diagonal
  summands `Hom(theta^d tensor gamma_l, S tensor gamma_l) = S^(direct sum d)`.
  So its top Chern class is divisible by `(c_d(S)^d)^N`, pulled back from
  `X_1`. The class `c_d(S)^d` lies in top degree `2d^2`, so its square vanishes.
  By Toms's identity the restricted `Delta_(d_L)` is `0`.

**Step 5: the failure in `A` (model test).** Choose `x in X_L` with
`h(x_l) = 1 - k_l/N`, possible when `h` maps onto `[0,1]`. Refinement only lowers
thresholds, so `b <= phi(b_L)` along the diagonal extension of `x`. Hence
`(b - (1-h))_+` vanishes along it, and `d_(tau_x)` of this element is `0`, while
`tau_x(h) = (1/N) sum_l (1 - k_l/N)` is about `1/2`. Square.
