---
rg: 2
id: leavitt-kl-violation-from-thompson-v-violation
kind: route
title: A violating equation over Thompson's V is a violating equation over the Leavitt unit group
target: kl-violating-equation-over-leavitt-unit-group
requires: [kl-violating-equation-over-thompson-v, leavitt-cylinder-swaps-generate-thompson-in-el]
---

Let `w in V * <t>` be nonsingular and let `1 != a in V` die in
`V_w = (V * <t>)/<<w>>`.

By `leavitt-cylinder-swaps-generate-thompson-in-el`, `V <= EL_D(R) <= R^x`
for `R = L_(F_2)(1,2)`. The inclusion `V * <t> -> R^x * <t>`, fixing `t`,
carries `<<w>>` into `<<w>>`, so it induces a homomorphism `V_w -> R^x_w`.
Hence `a` dies in `R^x_w`, while `a != 1` in `R^x`.

The word `w`, read with coefficients in `R^x`, is therefore a violation over
the Leavitt unit group. Its exponent sum is unchanged, so the violation is
nonsingular of the same degree.
