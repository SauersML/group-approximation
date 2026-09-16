---
rg: 2
id: z3-free-z-in-2v-as-a-raag
kind: route
title: Z^3 * Z is the right-angled Artin group of a triangle plus a point, so it lies in 2V
target: z3-free-z-embeds-in-brin-thompson-group-2v
requires:
  - every-raag-embeds-in-brin-thompson-group-2v
---

Let `Γ` have vertices `u_1, u_2, u_3, w`, with edges `{u_i, u_j}` for
`1 ≤ i < j ≤ 3` and no edge at `w`. The presentation of `A_Γ` is
`⟨t_1, t_2, t_3, s | [t_i, t_j] = 1⟩`. Here `⟨t_1, t_2, t_3⟩` with the
commutation relations presents `Z^3`, and `s` has no relation, so
`A_Γ = Z^3 * Z`. Since `Γ` is finite, `every-raag-embeds-in-brin-thompson-group-2v`
embeds `A_Γ` in `2V`. ∎
