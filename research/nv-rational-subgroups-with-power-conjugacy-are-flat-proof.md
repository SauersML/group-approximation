---
rg: 2
id: nv-rational-subgroups-with-power-conjugacy-are-flat-proof
kind: route
title: Transfer the zero-exponent conclusion along common powers, then test the landed tower at its hyperbolic fixed point
target: nv-rational-subgroups-with-power-conjugacy-are-flat
requires:
  - bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
  - rationals-embed-in-brin-thompson-group-2v
---

**Cocycle facts.** For `g, g' ∈ nV` and `x ∈ C^n`,
`δ_{g g'}(x) = δ_g(g' x) + δ_{g'}(x)`, since composing prefix replacements adds the
length changes coordinatewise. Hence if `g z = z`, then `δ_{g^j}(z) = j δ_g(z)` for
`j >= 1`, and `δ_{g^-1}(z) = -δ_g(z)`. So `δ_{g^j}(z) = j δ_g(z)` for all `j ∈ Z`.

**Item 1.** Let `h, f, m` be as in the statement, and let `h' ∈ D \ {1}`.
- By hypothesis on `D` there are nonzero integers `a, b` with `h'^a = h^b`. Put
  `w = h^b`. It is nontrivial, since `D` is torsion-free.
- `f w f^-1 = (f h f^-1)^b = h^{mb} = w^m`.
- Apply `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`, item 1, to
  `g = w`, `k = 1`, `l = m`. Its hypotheses are `k, l ≠ 0` and `|k| ≠ |l|`, which hold
  since `|m| >= 2`. So every periodic point `x` of `w`, of least period `p`, has
  `δ_{w^p}(x) = 0`.
- Let `z` be a periodic point of `h'` of least period `q`. Then
  `w^q z = (h'^q)^a z = z`, so `z` is `w`-periodic, with least period `p` dividing `q`.
- By the cocycle facts, `δ_{w^q}(z) = (q/p) δ_{w^p}(z) = 0`, since `w^p` fixes `z`.
  Also `δ_{w^q}(z) = δ_{(h'^q)^a}(z) = a δ_{h'^q}(z)`, since `h'^q` fixes `z`.
- Since `a ≠ 0`, `δ_{h'^q}(z) = 0`. So `h'` is exponent-flat. ∎

**Item 2.** Each listed group contains the element named in the statement, and the
relation holds:
- In `Aff(Q)`, `d_2 t_1 d_2^-1 = t_2 = t_1^2` with `d_2(x) = 2x`.
- In `SL_k(Q)`, `diag(2, 1/2, 1, …, 1) e_12(1) diag(2, 1/2, 1, …, 1)^-1 = e_12(4) = e_12(1)^4`.
  That diagonal matrix has determinant 1, so it lies in `B_k(Q)`, `SL_k(Q)` and
  `GL_k(Q)`. The same relation holds in the images `PSL_k(Q)` and `PGL_k(Q)`, where
  `e_12(1)` still has infinite order.

The translation or root subgroup is isomorphic to `(Q,+)`, and `φ` is injective, so
its image `D` satisfies the hypothesis of item 1 with `m = 2` or `m = 4`.

**Item 3.**
- By the landed construction, `s_0 = t × id`, and `s_0 ∈ R`.
- `t(00w) = 0w`. So `t(0^∞) = 0^∞`, and on the table brick `C(00) × C` the element
  `s_0` acts as `(00w, w') ↦ (0w, w')`. Its exponent vector is `(1 - 2, 0 - 0) = (-1, 0)`.
- So `(0^∞, y)` is a fixed point of `s_0` with `δ_{s_0} = (-1, 0) ≠ 0`, and `s_0` is
  not exponent-flat.
- Inside `nV`, `n >= 2`, with `2V` acting on the first two coordinates, the exponent
  is `(-1, 0, …, 0)`.

If some `h ∈ R \ {1}` were conjugate in `nV` to `h^m` with `|m| >= 2`, then item 1
would make every element of `R \ {1}` exponent-flat, including `s_0`. That is a
contradiction. The item-2 consequence follows. For a copy of `Q` containing an
element `g × id` with `g ∈ V`, a hyperbolic periodic point `x` of `g` of period `q`
gives the periodic point `(x, y)` with `δ = (δ_{g^q}(x), 0, …) ≠ 0`, and the same
argument applies. ∎
