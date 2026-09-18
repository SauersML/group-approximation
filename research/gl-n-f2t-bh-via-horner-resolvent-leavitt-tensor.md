---
rg: 2
id: gl-n-f2t-bh-via-horner-resolvent-leavitt-tensor
kind: route
title: F_2(t) inside the central simple Horner-resolvent algebra R_2 puts every GL_n(F_2(t)) in the Leavitt tensor unit group (R_2 ⊗ L)^x, finitely presented and simple once K_1 and K_2 vanish
target: gl-n-f2t-embeds-in-fp-simple-group
requires:
  - char-p-rational-function-field-in-fp-simple-algebra
  - horner-resolvent-leavitt-tensor-k1-k2-vanish
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
---

Let `R_2` be the algebra of `char-p-rational-function-field-in-fp-simple-algebra`
(`p = 2`), `L = L_(F_2)(1,2)`, and `A = R_2 ⊗ L`.

1. **The host.** `R_2` is a finitely presented central simple unital `F_2`-algebra (claim, parts 1
   and 4). By `horner-resolvent-leavitt-tensor-k1-k2-vanish`, `K_1(A) = K_2(A) = 0`.
   - `A^x` is simple: `central-simple-leavitt-tensor-unit-groups-are-simple`, part 2.
   - `A^x` is finitely presented: `leavitt-tensor-hosts-acyclic-steinberg-and-fp`, part 3
     (conditional on its imported criteria of Khanh).
2. **The embedding.** `F_2(t) ⊆ R_2` (claim, part 2), so
   `GL_n(F_2(t)) <= GL_n(R_2) <= GL_n(A) = M_n(A)^x`. Since `L ≅ L^2` as right `L`-modules,
   `L ≅ L^n` and `M_n(L) = End_L(L^n) ≅ L`, so `M_n(A) ≅ R_2 ⊗ M_n(L) ≅ A` as rings, and
   `GL_n(A) ≅ A^x`.
3. So every `GL_n(F_2(t))`, for all `n` simultaneously, embeds in the one finitely presented simple
   group `A^x`. `∎`

The route inherits the conditional status of `leavitt-tensor-hosts-acyclic-steinberg-and-fp`.
Its only open input is the `K`-theory gate.
