---
rg: 2
id: toms-block-diagonal-sharpening-fuzz-persistence-proof
kind: route
title: Brouwer degree on a product of paths forces all block traces onto half-integers at one point
target: toms-block-diagonal-sharpening-has-fuzz-persistence
requires: []
---

Imports from arXiv:2606.12188v2, Section 4: `X_(L+1) = X_L x X_L x CP^(j_L)` and
`phi_L(a) = (pi_1^* a tensor gamma_(L,1)) + (pi_2^* a tensor gamma_(L,2))`.
By induction `X_M = (X_L)^K x P` with `P` a product of projective spaces, the
copy maps `w -> w^(i)` are the coordinate projections onto the `K` factors, and
`phi_(L,M)(z)` restricted to `Q_i` has fibre `z(w^(i))` tensored with a line.
So `Tr (Q_i phi_(L,M)(z) Q_i)(w) = x(w^(i))`.

**Step 1: a product of paths.** `X_L` is connected. Choose `y_a, y_b` with
`x(y_a) = a`, `x(y_b) = b`, and a path `gamma: [0,1] -> X_L` from `y_a` to `y_b`.
Put `g = x o gamma`, so `g(0) = a`, `g(1) = b` and `g` takes values in `[a, b]`.
Fix `p_0 in P` and define `sigma: [0,1]^K -> X_M` by `sigma(t)^(i) = gamma(t_i)`
and projective coordinates `p_0`.

**Step 2: three maps of the cube.** On `[0,1]^K` put
- `Phi(t)_i = Tr e_i(sigma(t))`, continuous because `e` is;
- `G(t)_i = g(t_i)`;
- `Lambda(t)_i = a + (b - a) t_i`, an orientation-preserving homeomorphism onto `[a, b]^K`.
By hypothesis `|Phi(t)_i - G(t)_i| <= C` for all `t, i`.

**Step 3: the target point.** The interval `(a + C, b - C)` has length
`b - a - 2C > 2C + 2 >= 2`, so it contains a half-integer `c`. Put
`y* = (c, ..., c)`.

**Step 4: degree.** Use the straight-line homotopies `Phi ~ G` and `G ~ Lambda`.
Let `t` lie on the boundary of the cube, so some `t_i in {0, 1}`. Then
`G(t)_i = Lambda(t)_i in {a, b}`, and every map along either homotopy has
`i`-th coordinate within `C` of `a` or of `b`, hence different from `c`. So
neither homotopy meets `y*` on the boundary, and the Brouwer degrees agree:
`deg(Phi, (0,1)^K, y*) = deg(Lambda, (0,1)^K, y*) = 1`. Hence `Phi(t) = y*` for
some `t`. Put `w = sigma(t)`: every `Tr e_i(w)` equals the half-integer `c`.

**Step 5: defect.** Let `lambda_1, ..., lambda_n in [0,1]` be the eigenvalues of
`e_i(w)`.
- `lambda(1 - lambda) >= min(lambda, 1 - lambda)/2`, since the larger of
  `lambda, 1 - lambda` is at least `1/2`.
- Rounding each `lambda_j` to the nearer of `0, 1` gives an integer within
  `sum_j min(lambda_j, 1 - lambda_j)` of `sum_j lambda_j`.
So `Tr(e_i - e_i^2)(w) >= dist(Tr e_i(w), Z)/2 = 1/4`. The blocks lie in
orthogonal corners, so `e - e^2 = sum_i (e_i - e_i^2)` and
`Tr(e - e^2)(w) >= K/4`. The unit of `M_k(A_M)` has `Tr = k r_M = k K r_L`, which
gives the normalized bound `1/(4 k r_L)`.

**Step 6: model tests.**
- Prefix filling `Tr e_i = min(k r_L, max(0, S - (i-1) k r_L))` with
  `S = sum_j x(w^(j))`, realized by ramps through fixed chains of lines in each
  block, is continuous, block-diagonal and has at most one fractional block. It
  violates the displacement bound: at a point with alternating `x = a, b`
  blocks move by about `(b - a)/2` lines.
- The correction to the hypersimplex signpost is the case `C = 1`: a map fixing
  integer parts moves each block trace by at most one line. Square.
