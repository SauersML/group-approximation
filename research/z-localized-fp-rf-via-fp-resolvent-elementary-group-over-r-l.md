---
rg: 2
id: z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l
kind: route
title: A finite presentation of E_N(R_l) gives a finitely presented residually finite group containing Z_(l)
target: z-localized-embeds-in-fp-rf-group
requires:
  - resolvent-elementary-group-is-fp
  - resolvent-presentation-ring-is-residually-finite
  - z-localized-embeds-in-fp-kazhdan-steinberg-group
---

Take `l` and `N >= 5` from the first input. Then:
- `E_N(R_l)` is finitely presented, by the first input;
- it is residually finite, because `GL_N(R_l)` is when `R_l` is residually finite (reduce
  the entries of `g - I` into a finite quotient ring), and `R_l` is by the second input;
- `c -> e_12(θ(c))` is injective, because its composite with `E_N(R_l) -> E_N(R̄_l)` is
  (third input).

So `E_N(R_l)` witnesses the target. ∎
