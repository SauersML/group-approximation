---
rg: 2
id: z-localized-fp-rf-via-euler-triangular-steinberg
kind: route
title: The residually finite quotient of St_N(T_l) by a finitely normally generated finite residual contains Z_(l)
target: z-localized-embeds-in-fp-rf-group
requires:
  - euler-triangular-steinberg-rf-residual-is-fng
  - euler-base-embeds-in-fp-steinberg-group
---

Let `l`, `N >= 5` and `K_rf` be as in the first input.
- *Finitely presented.* `St_N(T_l)` is finitely presented (second input, item 1), so
  `Λ = St_N(T_l)/K_rf` is too.
- *Residually finite.* `Λ` is residually finite, being a group modulo its finite residual.
- *Contains `Z_(l)`.* `E_N(T_l)` is residually finite (second input, item 3), so its finite residual is
  trivial. Hence `K_rf` maps to 1 in `E_N(T_l)`, and `St_N(T_l) -> E_N(T_l)` factors through `Λ`. The
  composite `Z_(l) f_0 -> Λ -> E_N(T_l)`, `c -> e_12(ι(c f_0))`, is injective (second input, item 2), so
  `Z_(l)` embeds in `Λ`. ∎
