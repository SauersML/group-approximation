---
rg: 2
id: deligne-uniform-scalar-models-level-free-third-floor-proof
kind: route
title: Round the phase defect to an integral bounded cocycle, read both pieces in the one-dimensional H^2_b, and bound the error by the level-free Gromov norm
target: deligne-uniform-scalar-models-have-a-level-free-third-floor
requires: [sp4-lattice-bounded-cohomology-is-the-kahler-line, deligne-parameter-group-is-a-virtual-invariant]
---

Notation of the target. By its rephasing remark, work with the bounded integral representative `b'` of
`sp4-lattice-bounded-cohomology-is-the-kahler-line` (BK3), and write `b` for it. Cochains are inhomogeneous, and
`(delta f)(g,h) = f(g) + f(h) - f(gh)`, `(delta c)(g,h,k) = c(h,k) - c(gh,k) + c(g,hk) - c(g,h)`.

**Step 1 (rounding).** Choose `f : Lambda -> [0,1)` with `lambda = e(f)`, and set `x = delta f - theta b`, with a
fixed real lift of `theta`. Then `|e(x) - 1| = |lambda(g) lambda(h) - e(theta b) lambda(gh)| <= eps`, since
`|lambda(gh)| = 1`. Also `|e(x) - 1| = 2|sin(pi x)| >= 4 dist(x, Z)`. So `dist(x, Z) <= eps/4 < 1/4`.

Let `c` be the nearest integer to `x` and `s = x - c`, so `|s| <= eps/4` on all of `Lambda x Lambda`. Now `x` is
bounded (`|delta f| < 2` and `b` is bounded), so `c` is bounded. Since `delta x = -theta delta b = 0`, we get
`delta c = -delta s`. The left side is an integer and the right side has absolute value at most `4 (eps/4) < 1`.
So `delta c = delta s = 0`: both `c` (integral) and `s` (real) are bounded cocycles on `Lambda`.

**Step 2 (one-dimensional H^2_b).** `f` is bounded, so `delta f` is a bounded coboundary. In `H^2_b(Lambda)`,

```text
theta [b]_b + [c]_b + [s]_b = 0.
```

By (BK4), `[c]_b = t [b]_b` and `[s]_b = mu [b]_b`, with `theta + t + mu = 0`.

**Step 3 (`t in (1/2)Z`).** Apply the comparison map: `[c]_R = t [b]_R` in `H^2(Lambda;R)`. Put
`M = H^2(Lambda;Z)/Tors`, a lattice `Z^k` inside `H^2(Lambda;R)` (universal coefficients, as in (BK3)).
- `[b]` and `[c]` lie in `M`, and `[b] != 0` there. So `t` is rational: compare a coordinate where `[b]` is nonzero.
- Write `t = p/q` in lowest terms with `q > 0`. Then `q[c] = p[b]` in `M`. Choose `u, v` with `up + vq = 1`. Then
  `[b] = u p [b] + v q [b] = q (u [c] + v [b])` in `M`, so `[b|Lambda] in q H^2(Lambda;Z) + Tors`.
- By (V3) of `deligne-parameter-group-is-a-virtual-invariant`, `q in {1, 2}`. So `t in (1/2)Z`.

**Step 4 (norm).** `mu = -theta - t` with `t in (1/2)Z`, so `|mu| >= ||theta||_(1/2)`. Then

```text
||theta||_(1/2) nu_b <= |mu| ||[b]_b||_Lambda = ||[s]_b||_Lambda <= ||s||_inf <= eps/4,
```

using `||[b]_b||_Lambda = nu_b` from (BK4). This is (U1). At `theta = 1/3`, `||theta||_(1/2) = 1/6`.

**Step 5 ((U2)).** Write `U(g) = P_(sigma(g)) D(g)`, with `sigma(g)` a permutation of the index set `X` and `D(g)`
diagonal unitary.
- *Genuine action.* If `sigma(g) sigma(h) j != sigma(gh) j`, then `U(g)U(h) e_j` and `omega^b U(gh) e_j` are unit
  vectors on distinct coordinates. Their difference has norm `sqrt 2 > eps`. So `sigma` is a homomorphism.
- *Scalar model.* Fix `x in X` and let `Lambda = Stab(x)`, of index at most `d`. For `g in Lambda` put
  `lambda(g) = <U(g) e_x, e_x>`, a unit scalar because `U(g) e_x = lambda(g) e_x`. For `g, h in Lambda`,

  ```text
  lambda(g) lambda(h) - e(b/3) lambda(gh) = < (U(g)U(h) - e(b/3) U(gh)) e_x, e_x >,
  ```

  which has modulus at most `eps`.
- *Conclusion.* If `eps < 1`, (U1) gives `eps >= (2/3) nu_b`. Nothing depends on `X` or on `Lambda`.

**Step 6 ((U3)).** Block-monomial `U(g) = sum_j E_(sigma(g) j, j) (x) W_j(g)` with `W_j(g) in U(r)`.
- *Genuine action.* As in Step 5, using a unit vector in block `j`.
- *Block model.* For `g, h in Stab(x) = Lambda`, the `(x,x)` block gives
  `|| W_x(g) W_x(h) - e(b/3) W_x(gh) || <= eps`.
- *Determinant.* Put `Y = e(-b/3) W_x(g) W_x(h) W_x(gh)^*`. It is unitary with `||Y - I|| <= eps`, so each
  eigenphase satisfies `|phi_j| <= 2 arcsin(eps/2) <= (pi/2) eps`. Hence `|det Y - 1| <= (pi/2) r eps`.
  So `lambda = det W_x` is a scalar model on `Lambda` at parameter `r/3`, with defect `eps' <= (pi/2) r eps`.
- *Floor.* Since `3 not | r`, `||r/3||_(1/2) = 1/6`. So either `eps' >= 1` or `eps' >= (2/3) nu_b`, by (U1).

**Step 7 ((U4)).** These are direct consequences, since the floors of (U2) and (U3) do not depend on `Lambda`,
on the `Gamma`-set, or on the index. ∎

**Remark (why the w13 residue disappears here).** In Step 2 the class `[c]` is automatically in the image of
`H^2_b`, because `c = x - s` is bounded. The w13 residue `u = kappa + 3g` with `u_R` not proportional to `kappa_R`
has no bounded representative, since `image(H^2_b(Lambda) -> H^2(Lambda;R)) = R kappa` by (BK4). So `u` can arise as
`[c]` only when `s` is small on a window but unbounded, or not small, off it. That is the point-norm situation.
