---
rg: 2
id: toms-two-sibling-depth-two-proof
kind: route
title: Homotope the boundary of the target to the four-line diagonal loop inside the width-two rank band, and detect that loop by a Mayer-Vietoris class of degree seven
target: toms-two-sibling-swap-drops-add-to-depth-two
requires: []
---

Notation is from the target. Cohomology is singular, with rational coefficients.

**Step 1 (the band space).** For `n >= 1` let `X = X_g(n)` be the space of positive
`Q in M_n` with `g + 1 <= rank Q <= g + 2`, and `lambda_1 >= lambda_2 >= ...` its eigenvalues.
Cover it by open sets
- `U = {lambda_(g+1) > lambda_(g+2)}`, which contains all of rank `g + 1`, and
- `V = {rank Q = g + 2}`.

On `U` the span `W` of the top `g + 1` eigenvectors is a continuous bundle of rank `g + 1`
(holomorphic calculus with a contour separating `lambda_(g+1)` from `lambda_(g+2)`). On
`U ∩ V` the line `range Q ⊖ W` is continuous too. Let `y` be its first Chern class. Then
`omega = c_1(W) y^2` lies in `H^6(U ∩ V)`, and `Omega = delta(omega)` lies in `H^7(X)`, where
`delta` is the Mayer–Vietoris coboundary.

**Step 2 (evaluation on a loop).** Let `f : S^1 x Y -> X` be continuous. The open sets
`f^(-1) U`, `f^(-1) V` cover `S^1 x Y`, and by naturality `f^* Omega = delta'(f^* omega)`.
Suppose `S^1` is cut into closed arcs `A_1, ..., A_4` with cyclic vertices `v_a`, such that
- near `v_a`, `f` has rank `g + 1` with `W = F_a`, a bundle on `Y`;
- on the interior of the arc from `v_a` to `v_(a+1)`, `f` has rank `g + 2` with range `F_(a,a+1)`;
- on the part of that arc near `v_a` (resp. near `v_(a+1)`), `f` lies in `U ∩ V` with
  `W = F_a` (resp. `F_(a+1)`), and the quotient line `ell` has class `e_(a+1)` (resp. `e_a`).

Then `f^(-1)(U ∩ V)` contains eight intervals times `Y`, on which `f^* omega` is constant
along the interval. Computing `delta'` for the cover of the circle by vertex neighbourhoods
and arc interiors gives, under `H^7(S^1 x Y) ≅ H^6(Y)`,

```text
f^* Omega  =  ± sum_a [ c_1(F_a) e_(a+1)^2 - c_1(F_a) e_(a-1)^2 ].
```

A class pulled back from `U` depends only on `W` and has equal values at the two
intervals beside `v_a`. A class from `V` depends only on the range, which is `F_(a,a+1)`
at both ends of an arc. Both kinds cancel, so the formula depends only on `omega`
(checked in the artifact).

**Step 3 (the value).** In the target's situation `F_a = G ⊕ L_a` and
`e = (beta u_2, alpha u_1, alpha u_2, beta u_1)` in the order `b, r, t, l`. The terms with
`c_1(G)` telescope, and

```text
sum_a e_a (e_(a+1)^2 - e_(a-1)^2)  =  (alpha - beta)^2 (alpha + beta) (u_1 u_2^2 - u_1^2 u_2).
```

For `j >= 2` the monomials `u_1 u_2^2`, `u_1^2 u_2` are independent in `H^6(Y)`, so this is
non-zero exactly when `alpha != beta` and `alpha + beta != 0`.

**Step 4 (the model loop).** Choose the weights of `e` so that at every point of `∂S`
at most two `w_a` are positive, and they are adjacent. At the side midpoints only one
is. Then `e : ∂S x Y -> X_g(k)` is a loop of the form in Step 2. Near `v_a` it is
`P_G + P_a`. On the arc from side `a` to side `a+1` it is `P_G + w_a P_a + w_(a+1) P_(a+1)`.
Where `w_a > w_(a+1) > 0` it lies in `U ∩ V` with `W = G ⊕ L_a` and `ell = L_(a+1)`. So
`e^* Omega != 0` by Step 3. (If `P_G` has eigenvalue `1` below the weights, rescale `P_G`
by `2` first. This is a homotopy inside `X`.)

**Step 5 (the boundary of Q is homotopic to e).** Take the weights with
`w_a + w_(a+1) = 1` near each corner, so `max_a w_a >= 1/2` everywhere. Fix `0 < epsilon < 1/4`.
On `∂S x Y` we have `e <~ Q`, so by Rørdam's lemma there are `delta > 0` and `x` with
`e' := (e - epsilon)_+ = x (Q - delta)_+ x^*`. Now `e' = (1 - epsilon) P_G + sum_a (w_a - epsilon)_+ P_a`
is again a loop of the form in Step 4 (the weights `(w_a - epsilon)_+` have the same
pattern, and one of them is at least `1/4`). The path `(e - t epsilon)_+`, `t in [0,1]`,
stays in `X`, so `e'^* Omega = e^* Omega`. Replace `e` by `e'`.
Put `z = (Q - delta)_+^(1/2) x^*`. Then `z^* z = e` and `z z^*` lies in the hereditary
subalgebra of `(Q - delta)_+`, so `range(z z^*) ⊆ range Q` at every point.
- *From `Q` to `z z^*`.* `Q_t = (1 - t) Q + t z z^*` has range `range Q` for `t < 1`,
  and `z z^*` at `t = 1`. Its rank lies in `[rank e, rank Q] ⊆ [g + 1, g + 2]`.
- *From `z z^*` to `e`.* In `M_(2n)`, `Z_theta = [cos theta z ; sin theta e^(1/2)]` has
  `Z_theta^* Z_theta = e`. So `Z_theta Z_theta^*` has the non-zero spectrum of `e` and lies in
  `X_g(2n)`. It runs from `z z^* ⊕ 0` to `0 ⊕ e`.

The inclusions `X_g(n) -> X_g(2n)` are compatible with `U`, `V`, `W` and `ell`. So
`(Q|∂S)^* Omega = e^* Omega != 0` in `H^7(S^1 x Y)`.

**Step 6 (conclusion).** Suppose `rank Q >= g + 1` on all of `S x Y`. Then
`Q : S x Y -> X_g(n)`, and `Q|∂S` factors through `S x Y`. But `H^7(S x Y) ≅ H^7(Y) = 0`,
since `Y` has only even cohomology, so `(Q|∂S)^* Omega = 0`. This contradicts Step 5.
Hence `rank Q <= g` somewhere. On `∂S` the rank is at least `rank e >= g + 1`, so that
point is interior.

**Step 7 (the consequence).** The check that `e <= C P` in the window box is the
paragraph in the target. The upper band gives `rank Q <= m`, and in the staggered
model `m = 2R = g + 2`, with `g = 2(R - 1)` from the other pairs. Square.
