---
rg: 2
id: braid-z-linearity-via-lkb-unit-specialization
kind: route
title: Braid groups are Z-linear if Lawrence–Krammer survives a specialization at algebraic units
target: every-braid-group-embeds-in-some-glnz
requires:
  - lawrence-krammer-has-a-faithful-algebraic-unit-specialization
  - faithful-unit-specialization-gives-z-linearity
---

Fix `n`. The first premise gives a number field `F` and units `q_0, t_0` of
`O_F` at which the Lawrence–Krammer representation `rho` of `B_n`, with entries
in `Z[q^{±1}, t^{±1}]`, stays injective. The second premise, applied with
`k = 2` and `x_1 = q`, `x_2 = t`, embeds `B_n` in
`GL_((n(n-1)/2)[F:Q])(Z)`. Since `n` was arbitrary, every braid group embeds in
some `GL_m(Z)`.
