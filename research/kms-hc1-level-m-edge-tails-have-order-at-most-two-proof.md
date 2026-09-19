---
rg: 2
id: kms-hc1-level-m-edge-tails-have-order-at-most-two-proof
kind: route
title: Edge tails live in u(heis), whose letter degrees stop at 2p-2, so torus shifts are 0 or p-1 per letter; PBW counting empties the (2p,2,2p) slice, and invariance of the trace kills the Kassel part of every Jacobson word of a t^m-homogeneous element
target: kms-hc1-level-m-edge-tails-have-order-at-most-two
requires: [kms-hc1-witt-carry-syzygy-lifts-by-right-freeness, kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations]
artifacts:
  - experiments/kms-hc1-level-m-tails-2026-09-18/heis_defect.py
  - experiments/kms-hc1-level-m-tails-2026-09-18/heis_defect_p11.out
---

Notation of the claim. Fix `p >= 5`.

## 1. The tail bound (T1)

Let `r` be an edge relator on the edge `{x,y}`.

- **rho(r-1) lies in u(h_xy).** The images `rho(Y_x)` and `rho(Y_y)` lie in
  `h_xy`, so `rho` maps `F_p<<Y_x,Y_y>>` into `u(h_xy)`.
- **Every monomial involves both letters.** Setting `Y_y = 0` sends `r` to
  1. So the part of `r-1` that has no `Y_y` is zero, and likewise for `Y_x`.
  Hence every monomial of every eigencomponent `f_r{c}` has `x`- and
  `y`-degree at least 1. The same holds for the part of `rho(f)` in each
  bidegree.
- **Degree cap.** The PBW monomial `x^i e^k y^j` has `x`-degree `i+k`,
  which is at most `2p-2`. So any `rho`-visible bidegree `d` has `d_x` in
  `[1, 2p-2]`.
- **Conclusion.** The torus lemma gives `d_x ≡ c_x (mod p-1)` with `c_x` in
  `[1,p-1]`. So `d_x` is `c_x` or `c_x+p-1`, and the same holds for `y`.
  The shift `(d-c)/(p-1)` therefore lies in `{0,1}^2`.

If the lowest form of `f_r{c}` sits in degree `d0 >= c`, the tails measured
from `d0` have even fewer shifts. A single-letter shift `2(p-1)` would need
`d_x >= 1 + 2(p-1) > 2p-2`. ∎

## 2. The shape (T2)

The script `heis_defect.py` works in `u(h)` with the basis `a^i e^k b^j`.

- It uses left multiplication by `a` and by `b`, where
  `b a^i = a^i b - i a^(i-1) e`.
- It computes `D(lambda,mu) = r(E(lambda a), E(mu b)) - 1` for all
  `(lambda,mu)`, and projects onto each class `c`.
- Because `rho` is graded, the projection is the class-`c` part of
  `D(1,1)`.

For each class it lists the support and checks four things:
- every shift lies in `{0,1}^2`;
- no letter degree is 0;
- the shift `(0,0)` is absent;
- which single-letter shifts occur.

It prints `ALL SHIFTS IN {0,p-1}^2: True` at `p = 5, 7, 11`, and each
relator type shows exactly one single-letter shift (`heis_defect_p*.out`).

## 3. The empty slice (T3)

The multidegree of `X t^k`, for a root `(n1,n2)` of `sl3`, is
`(k+n1, k+n2, k)`.

- **Multidegree `(2,2p-1,0)`.** c-degree 0 forces `k = 0`, so the only
  factors are `E12`, `E23` and `E13`. In a PBW monomial `E12^i E23^j E13^k`
  with exponents below `p`, the b-degree is `j+k <= 2p-2`. So the space is
  zero.
- **Multidegree `(0,2p-1,2)`.** a-degree 0 allows only `E23`, `E31 t` and
  `E21 t`, with multidegrees `(0,1,0)`, `(0,0,1)` and `(0,1,1)`. c-degree 2
  forces at most two `t`-factors. So the b-degree is `j + k <= (p-1) + 2`,
  which is less than `2p-1` for `p >= 5`. The space is zero.

So `rho(f2) = 0` for both seeds. A term with overlap in `(2p,2,2p)` reaches
b-degree `2p` only through a b-shift `2(p-1)`, and (T1) excludes that. ∎

## 4. Localization (T4)

Write `rho(T) = sum c_i rho(u_i) rho(g_i) rho(v_i)`. Each `g_i` is one of
three kinds.

- **Edge eigencomponent.** `rho(g_i)` is the sum of its tails. The
  `(mp,mp,mp)` part of the term needs a tail of shift `s` with
  `deg u_i + d0(g_i) + deg v_i + (p-1)s = (mp,mp,mp)`, and (T1) allows only
  `s` in `{e_x, e_y, e_x+e_y}`. Shift `s=0` gives `rho(g_i^lowest) = 0`,
  since the Serre relations hold in `N`.
- **`Y_x^p`.** It maps to a p-th power of a root vector, which is 0 in
  `u(N)`.
- **`(Y_xY_y - Y_yY_x)^p`.** It maps to `e_xy^[p] = 0`.

At `m = 2` this leaves the following nine (edge, shift) pairs:

| edge | overlap for `e_x` | overlap for `e_y` | overlap for `e_x+e_y` |
|---|---|---|---|
| ab | `(p+1,2p,2p)` | `(2p,p+1,2p)` | `(p+1,p+1,2p)` |
| bc | `(2p,p+1,2p)` | `(2p,2p,p+1)` | `(2p,p+1,p+1)` |
| ca | `(2p,2p,p+1)` | `(p+1,2p,2p)` | `(p+1,2p,p+1)` |

At `m = 1` a diagonal overlap `(1,1,p)` with edge `ab` would contain `g_i`
of `ab`-degree 2. But every edge eigencomponent has total degree at least 3
(its lowest form is a Serre word). So no diagonal slice occurs. ∎

## 5. The level-m p-map (T5)

In `N` the cocycle pairs `x t^i` and `y t^j` to
`i delta_(i+j, mp) kappa tr(xy) z` at level `m`.

1. **Setup.** Let `u = Y t^m` and `v = X t^m`. By Jacobson,
   `(u+v)^[p] = u^[p] + v^[p] + sum s_i(u,v)`, where `i s_i` is the
   coefficient of `lambda^(i-1)` in `ad(lambda u + v)^(p-1)(u)`.
2. **Reduction to the outermost bracket.** Put `W = lambda u + v` and
   `R = ad(W)^(p-2)(u)`. Inner brackets land in `t`-degrees `km` with
   `k < p`. Any central part they produce is killed by the next `ad(W)`. So
   `R` is its `sl3 t^(m(p-1))` component, and the `z`-part of `[W,R]` is
   `m kappa tr(W_0 R_0) z`, where `W_0` and `R_0` are the `sl3`-parts.
3. **The trace vanishes.** `R_0 = [W_0, R'_0]`, so
   `tr(W_0 [W_0, R'_0]) = tr([W_0,W_0] R'_0) = 0`. This uses only `p >= 3`,
   since then `R` is a bracket.
4. **Additivity.** So the `z`-part of the p-map is additive on
   `sl3 t^m`, and p-semilinear.
5. **Evaluation.** Root vectors have p-map 0, and `(h t^m)^[p]` has
   `z`-part `alpha(h)`. With `c^p = c` in `F_p`, this gives the formula.

For `W = u' + u''` of different `t`-degrees, `R` has several `t`-degrees,
and the pairing `i delta` then weights them differently. The formula fails
there. ∎
