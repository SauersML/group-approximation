---
rg: 2
id: euler-triangular-residual-fng-from-fg-central-k2
kind: route
title: A finitely generated central K_2 makes the finite residual of St_N(T_l) finitely normally generated
target: euler-triangular-steinberg-rf-residual-is-fng
requires:
  - euler-triangular-ring-has-fg-central-unstable-k2
  - euler-base-embeds-in-fp-steinberg-group
---

Take `l` and `N >= 5` from the first input, so `K = K_2(N, T_l)` is central and finitely generated.
- `E_N(T_l)` is residually finite (second input), so the finite residual `K_rf` of `St_N(T_l)` lies in `K`.
- `K` is abelian, being central, and finitely generated. So its subgroup `K_rf` is finitely generated,
  because finitely generated abelian groups are Noetherian.
- `K_rf` is central, so its normal closure in `St_N(T_l)` is `K_rf` itself. So `K_rf` is the normal closure
  of a finite set. ∎
