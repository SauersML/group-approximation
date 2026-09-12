---
rg: 2
id: leavitt-power-projective-e-fp-from-trivial-k-theory
kind: route
title: Vanishing K_1 and K_2 make E_m of the tensor power its finitely presented unit group
target: leavitt-power-projective-elementary-groups-finitely-presented
requires:
  - prime-field-leavitt-tensor-powers-have-trivial-k-theory
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

Let `R_d = L_p^(⊗d) = R_(d-1) ⊗ L_p`.

1. **Hypotheses.** `R_(d-1)` is a simple, finitely presented `F_p`-algebra: a
   tensor product of simple central algebras and of finitely presented algebras
   over a field.
2. **Unit group.** If `K_1(R_d) = K_2(R_d) = 0`, then parts 2 and 3 of
   `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` give
   `GL_m(R_d) = E_m(R_d)` for `m >= 2`, and `R_d^x` finitely presented.
3. **Every rank.** `M_m(R_d) ≅ R_d` for every `m` (Ara--Goodearl--Pardo, since
   `gcd(m, 1) = 1`). So `E_m(R_d) = GL_m(R_d) ≅ R_d^x` is finitely presented.
4. **Centre.** Its centre is finite, so the quotient is finitely presented for
   every `m >= 2`.
