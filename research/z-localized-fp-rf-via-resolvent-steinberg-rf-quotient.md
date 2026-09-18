---
rg: 2
id: z-localized-fp-rf-via-resolvent-steinberg-rf-quotient
kind: route
title: The residually finite quotient of St_N(R_l) by a finitely normally generated finite residual witnesses the Z_(l) bottleneck
target: z-localized-embeds-in-fp-rf-group
requires:
  - resolvent-steinberg-rf-residual-is-finitely-normally-generated
  - resolvent-presentation-ring-is-residually-finite
  - z-localized-embeds-in-fp-kazhdan-steinberg-group
  - steinberg-groups-of-fp-rings-are-fp-in-rank-five
---

Let `l` and `N >= 5` be as in the first input, and `K_rf` the finite residual of
`St_N(R_l)`.
- *Finitely presented.* `St_N(R_l)` is finitely presented (rank-five node), and `K_rf` is
  the normal closure of finitely many elements. So `Λ = St_N(R_l)/K_rf` is finitely
  presented.
- *Residually finite.* A group modulo its finite residual is residually finite: every
  finite quotient of `St_N(R_l)` factors through `Λ`, and together they separate `Λ`.
- *Contains Z_(l).* `R_l` is residually finite, so `GL_N(R_l)` and `E_N(R_l)` are.
  - The image of `K_rf` in `E_N(R_l)` lies in the finite residual of `E_N(R_l)`, which
    is trivial. So `St_N(R_l) -> E_N(R_l)` factors through `Λ`.
  - The composite `c -> x_12(θ(c)) -> e_12(θ(c))` into `E_N(R_l)` is injective. Its
    image in `E_N(R̄_l)` is injective by `z-localized-embeds-in-fp-kazhdan-steinberg-group`.
  - So `Z_(l)` embeds in `Λ`. ∎
