---
rg: 2
id: counting-ring-steinberg-group-has-every-torsion-order-proof
kind: route
title: Krstić–McCool finite presentation, additive root-subgroup torsion and matrix detection over the residually finite counting ring
target: counting-ring-steinberg-group-has-every-torsion-order
requires:
  - counting-ring-is-residually-finite-with-every-additive-order
  - steinberg-finite-presentation-and-kazhdan-theorem
---

Let `R = R_count` and `G = St_m(R)` with `m >= 4`. The generators are `x_ij(r)`,
subject to `x_ij(r) x_ij(s) = x_ij(r+s)` and the commutator relations. Let
`pi : G -> E_m(R) <= GL_m(R)` be the natural map, `pi(x_ij(r)) = 1 + r E_ij`.

**(S1).** `R` is finitely presented as a unital ring (three generators, three
relations). `steinberg-finite-presentation-and-kazhdan-theorem` gives that `G`
is finitely presented and has property (T). It quotes Ershov--Jaikin-Zapirain,
arXiv:0809.4095v2 §6.1, verbatim:

> "By a theorem of Krstić and McCool [KrM, Theorem 3], the Steinberg group
> St_n(R) is finitely presented for any n ≥ 4 and any finitely presented ring R,
> in particular for R = Z⟨x1, . . . , xd⟩."

Their Theorem 6.2 reads: "The Steinberg group St_n(R), n ≥ 3, has property (T)."
The ring `R` there is finitely generated.

**(S2).** By the additivity relation, `x_12(r_n)^k = x_12(k r_n)`. By (C1) of
`counting-ring-is-residually-finite-with-every-additive-order`, `k r_n = 0`
exactly when `n | k`. So `x_12(r_n)^n = 1`.

For `0 < k < n`, `pi(x_12(r_n)^k) = 1 + k r_n E_12 != 1`. So the order is exactly
`n`. Compose with the ring map `rho_n : R -> M_n(Z/n)` of (C2). The image
`1 + k E_00 E_12` in `GL_m(M_n(Z/n))` is nontrivial for `0 < k < n` and trivial
for `k = n`. `E_m(M_n(Z/n))` is finite, so this is a finite quotient of `G` in
which the order is still `n`. `∎`

**(S3).** Let `g` lie outside `ker pi`. Then `pi(g) - 1` has a nonzero entry
`s` in `R`. By (C3) there is a ring map `phi : R -> S` into a finite ring with
`phi(s) != 0`. The composite `G -> GL_m(R) -> GL_m(S)` has finite image and does
not kill `g`. So `g` is not in `G_res`. `∎`

**(S4).** `G / G_res` is residually finite by definition of the finite residual.
It is finitely generated because `G` is. It has property (T) as a quotient of `G`.
Each finite quotient in (S2) factors through `G / G_res`. So the image of
`x_12(r_n)` there has order divisible by `n`, while its `n`-th power is trivial.
Hence its order is exactly `n`. `∎`

**Consequence.** If `G_res` is the normal closure of `h_1, ..., h_s`, then
`G / G_res` is the finitely presented group obtained by adding `h_1, ..., h_s`
as relators. `∎`
