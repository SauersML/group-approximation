---
rg: 2
id: deligne-maslov-tensor-functors-are-asymptotically-regular-proof
kind: route
title: Push a one-third model into the tracial ultraproduct, read its trace off the central-regular classification, and multiply traces
target: deligne-maslov-tensor-functors-are-asymptotically-regular
requires: [deligne-maslov-sector-traces-are-central-regular, deligne-sep7-norm-parameter-closed-subgroup, deligne-sep7-all-cover-mf-radical-classification]
---

Notation of the target. `E_infinity = Gamma x_b Z` with product `(g,j)(h,l) = (gh, j + l + b(g,h))` and central
generator `z = (e,1)`; `E_3 = E_infinity / <z^3>`. For a free ultrafilter `w` on `N`, `M^w` is the tracial
ultraproduct of `(M_(d_n), tr)` and `tau_w` its trace. `||x||_2 = tr(x* x)^(1/2)`.

**Step 1. A `1/3`-model is a representation of the twisted fibre.** Put `Theta(g,j) = omega^j [U_n(g)]_n` in `Q`.
Then

```text
Theta(g,j) Theta(h,l) = omega^(j+l) [U_n(g) U_n(h)] = omega^(j+l) omega^(b(g,h)) [U_n(gh)] = Theta((g,j)(h,l)),
```

the middle equality holding in `Q` because the pointwise defect tends to `0`. Each `Theta(g,j)` is unitary in `Q`
(the `U_n(g)` are unitary), `Theta(z) = omega`, and `Theta(z^3) = 1`. So `Theta` is a unitary representation of
`E_3` in `Q` with `z -> omega`. The quotient map `Q -> M^w` is a unital `*`-homomorphism: a `c_0`-sequence has
operator norms, hence normalized HS norms, tending to `0`. Composing, `pi_w : E_3 -> U(M^w)` is a unitary
representation with `pi_w(z) = omega`. By the universal property it extends to `C*(E_3)` and kills `z - omega`, so it
factors through `A_omega = C*(E_3)/(z - omega)`. Therefore `phi = tau_w o pi_w` is a tracial state on `A_omega`.

**Step 2. Regular trace (item 1).** By `deligne-maslov-sector-traces-are-central-regular`, `phi` is a convex
combination of the central-regular traces `tau_eta`, which vanish off `Z(E_3)`. `Z(E_3)` is the preimage of
`{+I, -I}`, so for non-central `g`,

```text
lim_w tr U_n(g) = tau_w(pi_w(g,0)) = phi(g,0) = 0.
```

This holds for every free ultrafilter `w`. A bounded complex sequence all of whose ultrafilter limits are `0`
tends to `0`, so `tr U_n(g) -> 0`. For the functor, `tr(A (x) B) = tr(A) tr(B)` for normalized traces and
`tr(conj A) = conj(tr A)`, so

```text
| tr F_n(g) | = | tr U_n(g) |^(a + c) | tr R_n(g) |  <=  | tr U_n(g) |^(a + c)  ->  0,
```

using `|tr R_n(g)| <= 1` for unitary `R_n(g)` and `a + c >= 1`. No property of `R_n` is used.

**Step 3. Distance to scalars (item 2).** For a unitary `X` and `mu in C`,

```text
|| X - mu I ||_2^2 = tr(X* X) - 2 Re( conj(mu) tr X ) + |mu|^2 = 1 + |mu|^2 - 2 Re( conj(mu) tr X ).
```

With `X = F_n(g)` and `tr X -> 0`: if `|mu_n|` stays bounded, the right side is `1 + |mu_n|^2 - o(1) >= 1 - o(1)`;
if `|mu_n| -> infinity` along a subsequence, it tends to infinity there. So the liminf of the distance is at least
`1`. When `|mu_n| = 1`, the squared distance is `2 - o(1)`, so the distance tends to `sqrt 2`. The normalized HS norm is at most the operator norm, so the same bounds hold in operator norm.

**Step 4. Comparison (items 3 and 4).** For unitaries `X, Y` of the same size, `|tr X - tr Y| = |tr(X - Y)| <=
||X - Y||_2` by Cauchy--Schwarz. With `X = F_n(g)`, `Y = rho_n(g)`: `|tr rho_n(g)| <= eps + |tr F_n(g)| = eps + o(1)`.
- If `rho_n(g) = I`, Step 3 with `mu_n = 1` gives `||F_n(g) - I||_2 -> sqrt 2`.
- *Finite image.* Let `Psi : Gamma -> U(Q')` be a homomorphism with finite image, and `Lambda = ker Psi`, of finite
  index in `Gamma`. `Lambda` is infinite and `{+I, -I}` is finite, so `Lambda` contains a non-central `g`, with
  `Psi(g) = 1`. The quotient `Q' -> M^w` is contractive for the operator norm on `Q'` and the `2`-norm on `M^w`
  (`||x||_2 <= ||x||` on each coordinate). If `||F(g) - Psi(g)||_(Q') < 1`, then `||pi_F(g) - 1||_2 < 1` in `M^w`, where
  `pi_F` is the image of `F` in `M^w`. That contradicts `||pi_F(g) - 1||_2 = sqrt 2`, which is Step 3 in `M^w`.
- *Bounded level.* Honest representations `rho_n` with `ker rho_n` containing one fixed finite-index `Lambda`
  (bounded level) have `rho_n(g) = I` for every `g in Lambda`. The same non-central `g in Lambda` gives HS distance
  `sqrt 2 - o(1)`.
- *Item 4.* For each non-central `g`, `|tr rho_n(g)| <= eps + o(1) < 1` eventually. Since `tr rho_n(g) = 1` whenever
  `g in ker rho_n`, the element `g` lies in only finitely many `ker rho_n`. Hence no finite-index subgroup lies in
  infinitely many kernels: the level is unbounded along every subsequence, and the characters of `rho_n` are
  asymptotically `eps`-small off the center.

**Step 5. The w8 conditional is equivalent to the flagship.** The w8 attempt proved: if every tensor cube of every
`1/3`-model is `Q`-close to a homomorphism with finite image, then `1/3 not in P_op`. Step 4 (`a = 3`, `c = 0`,
`R = 1`) shows that the hypothesis fails for the cube of any `1/3`-model. So the hypothesis holds iff no `1/3`-model
exists, iff `1/3 not in P_op`. By `deligne-sep7-all-cover-mf-radical-classification`
(`Rad_MF(E_q) = {z_q^k : exp(2 pi i k theta) = 1 for all theta in P_op cap (1/q)Z/Z}`, applied with `q = 3`), this is
`Rad_MF(E_3) = C_3`, the flagship. The conditional is a tautology.

**Remark (conditional; not part of the established statement).** A level-free argument works in the *uniform*
category. Suppose `U : Gamma -> U(d)` has sup defect at most `eta` against `omega^b` on `Lambda x Lambda`, where
`Lambda` has finite index. Suppose also `||U(g) - lambda(g) I|| <= eta'` on `Lambda`, with `lambda(g) = e(f(g))`.
Put `eps = eta + 3 eta'`. Then

```text
f(g) + f(h) - f(gh) - b(g,h)/3 = c(g,h) + s(g,h),   c integral,  |s| <= eps/4.
```

For `eps < 1`, `delta c = delta s = 0`. So `[b]/3 + [c] + [s] = 0` in `H^2_b(Lambda, R)`, read through the
comparison map. *If* `H^2_b(Lambda, R) = R [b]`, then `[s] = mu [b]` with `|mu| <= ||s||_inf / ||[b]||`, where the
Gromov norm of `[b]` on `Lambda` equals that on `Gamma` by transfer. Then `(1/3 + mu)[b]` is integral modulo
torsion. The divisibility set `{1, 2}` of `deligne-parameter-group-is-a-virtual-invariant` forces `|mu| >= 1/6`,
which is a contradiction when `eps < (2/3) ||[b]||`.

The missing input is the non-cocompact Burger--Monod statement `H^2_b(Lambda, R) = R [b]` for finite-index
`Lambda < Sp_4(Z)`. The verified abstract of Burger--Monod, JEMS 1 (1999), DOI 10.1007/s100970050007, covers only
*cocompact* lattices. The argument dies in point-norm, because there `s` is small only on finite windows, not as a
bounded cocycle on all of `Lambda`.
