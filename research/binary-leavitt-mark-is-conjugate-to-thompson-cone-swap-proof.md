---
rg: 2
id: binary-leavitt-mark-is-conjugate-to-thompson-cone-swap-proof
kind: route
title: Read the three-factor swap identity as a conjugacy and transport the mark through the Morita chain
target: binary-leavitt-mark-is-conjugate-to-thompson-cone-swap
requires:
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-prime-field-units-generated-by-v-and-one-transvection
  - leavitt-steinberg-map-iso-from-rank-three
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-elementary-group-is-simple
---

Conventions: `s_w` and `t_w = s_w^*` are the path products, `e_w = s_w t_w`.
For incomparable words `a`, `b`, the Cuntz--Leavitt relations give
`t_a s_a = 1` and `t_a s_b = 0 = t_b s_a`.

**Part 1.**
- `tau^2 = 1 + 2 s_a t_b + s_a (t_b s_a) t_b = 1`, since the characteristic is
  two and `t_b s_a = 0`. The same holds for `h`.
- Expanding, `tau h = 1 + s_a t_b + s_b t_a + s_a (t_b s_b) t_a
  = 1 + s_a t_b + s_b t_a + e_a`.
- Multiply on the left by `h = 1 + s_b t_a` and use `t_a s_a = 1`,
  `t_a s_b = 0`. Left multiplication by `s_b t_a` sends the four terms
  `1, s_a t_b, s_b t_a, e_a` to `s_b t_a, e_b, 0, s_b t_a`. So

```text
h tau h = (1 + s_a t_b + s_b t_a + e_a) + (s_b t_a + e_b + s_b t_a)
        = 1 + e_a + e_b + s_a t_b + 3 s_b t_a
        = 1 + e_a + e_b + s_a t_b + s_b t_a = sigma.
```

- By the symmetry `a <-> b`, which swaps `tau` and `h` and fixes `sigma`, also
  `tau h tau = sigma`. This is the identity `sigma = (1+P)(1+Q)(1+P)` of
  `leavitt-cylinder-swaps-generate-thompson-in-el`.
- Then `(tau h)^3 = (tau h tau)(h tau h) = sigma^2 = 1`. Also `tau h != 1`,
  since `tau != h` (their difference `s_a t_b + s_b t_a` is nonzero). So
  `<tau, h>` is dihedral of order six, which is `S_3`.

**Part 2.** `leavitt-prime-field-units-generated-by-v-and-one-transvection`
gives `R^x = <V, tau>` for `tau = 1 + s_00 t_01`. By Part 1,
`tau = h sigma h` with `sigma in V`, so `tau` lies in `V^h`. Hence
`R^x = <V, V^h>`.

**Part 3.**
- `leavitt-steinberg-map-iso-from-rank-three` gives `St_20(R) -> GL_20(R)`, an
  isomorphism sending `z` to `e_13(s_1 t_1)`.
- Choose a complete binary prefix code `u_1, ..., u_20`. The prefix-code
  self-similarity of `leavitt-gl-equals-el-and-perfect-unit-group` is
  `Theta(x) = sum_(i,j) s_(u_i) x_ij t_(u_j)`, which gives
  `GL_20(R) ~= R^x`. It sends the identity to `sum_i e_(u_i) = 1`, and
  `e_13(r)` to `1 + s_(u_1) r t_(u_3)`.
- For `r = s_1 t_1` this is `1 + s_alpha t_beta` with `alpha = u_1 1` and
  `beta = u_3 1`. These are incomparable because `u_1` and `u_3` are distinct
  leaves of a prefix code.
- Part 1 conjugates it to the cylinder swap of `alpha` and `beta`, which lies in
  `V` (`leavitt-cylinder-swaps-generate-thompson-in-el`).

**Part 4.**
- `Delta ~= EL_20(R)` is simple by `binary-leavitt-elementary-group-is-simple`
  and `GL = EL`.
- A normal subgroup containing one nonidentity element is everything.
- `z`, `sigma` and `V` are all nontrivial, and `z` is conjugate to `sigma`, so
  the four conditions are equivalent.

No step uses property (T).
