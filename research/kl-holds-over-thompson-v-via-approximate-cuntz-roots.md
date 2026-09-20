---
rg: 2
id: kl-holds-over-thompson-v-via-approximate-cuntz-roots
kind: route
title: Approximate roots in U(O_2) become exact roots in the norm ultrapower, which contains V faithfully
target: kl-holds-over-thompson-v
requires:
  - thompson-v-equations-have-approximate-cuntz-unitary-roots
---

Let `w in V * <t>` have nonzero `t`-exponent sum, and let `a in V` die in `V_w = (V * <t>)/<<w>>`.

## Step 1: the canonical copy is a faithful homomorphism

For `g in V`, choose complete prefix codes `(u_i)` and `(v_i)` such that `g` maps the cone `u_i` onto the cone `v_i` by
prefix replacement. Put `U_g = sum_i s_(v_i) s_(u_i)^*`.

- **Well defined.** `s_u s_v^* = s_(u0) s_(v0)^* + s_(u1) s_(v1)^*`, and any two code pairs for `g` have a common
  refinement. So `U_g` does not depend on the codes.
- **Homomorphism.** Given `g` and `h`, refine so that `h` maps `u_i -> v_i` and `g` maps `v_i -> x_i`. Words in a prefix
  code are pairwise incomparable, so `s_(v_i)^* s_(v_j) = delta_ij`. Hence `U_g U_h = sum_i s_(x_i) s_(u_i)^* = U_(gh)`.
  Each `U_g` is unitary, since `sum_i s_(v_i) s_(v_i)^* = 1` for a complete code.
- **Faithful.** Suppose `U_g = 1`. Then `s_(v_i) = U_g s_(u_i) = s_(u_i)` for each `i`. If `u != v` are words, then
  `s_v^* s_u` is `0` when they are incomparable. When `v` is a proper prefix of `u`, say `u = v u'`, it equals `s_(u')`,
  a non-unitary isometry. In neither case is `s_u = s_v`. So `u_i = v_i` for all `i`, and `g = 1`.

## Step 2: an exact root in the ultrapower

By the prerequisite, pick `T_n in U(O_2)` with `||w(U, T_n) - 1|| < 1/n`. Fix a free ultrafilter `omega` on `N`, and let
`O_2^omega = l^infinity(N, O_2)/c_omega`.

- `T = [T_n]` is a unitary of `O_2^omega`.
- Multiplication is coordinatewise, so `w(U, T) = [w(U, T_n)] = 1`.
- The diagonal map `O_2 -> O_2^omega` is an isometric unital `*`-homomorphism.

## Step 3: injectivity

Define `psi : V * <t> -> U(O_2^omega)` by `g ↦ U_g` (diagonally) and `t ↦ T`. Then `psi(w) = 1`, so `psi` factors
through `V_w`.

The composite `V -> V_w -> U(O_2^omega)` is the diagonal copy of the canonical map. It is injective by Step 1 and the
isometry of the diagonal map. So `a = 1`.

Hence the coefficient map `V -> V_w` is injective, which is `kl-holds-over-thompson-v`.
