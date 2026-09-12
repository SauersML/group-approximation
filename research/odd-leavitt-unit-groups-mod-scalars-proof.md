---
rg: 2
id: odd-leavitt-unit-groups-mod-scalars-proof
kind: route
title: Apply the prime-field host theorem with B = F_p and B = L_p, using K-theory vanishing over F_p
target: odd-leavitt-unit-groups-mod-scalars-are-fp-simple
requires:
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
  - leavitt-center-is-coefficient-field
artifacts:
  - research/artifacts/boone-higman-prime-field-leavitt-hosts-2026-09-12.md
---

This is artifact Theorem 5.1.

1. **`K`-theory.** `ara-cortinas-leavitt-tensor-k-theory-vanishes` holds over
   every field.
   - With `R = F_p`, a regular Noetherian field, `K(L_p) = 0`.
   - `L_p` is regular supercoherent by Lemma 6.1 there, so `K(L_p ⊗ L_p) = 0`.
2. **Coefficients.**
   - `B = F_p` and `B = L_p` are central simple: `leavitt-center-is-coefficient-field`
     holds for every field, and `L_p` is simple by the division property.
   - Both are finitely presented rings: `p, se-1, tf-1, sf, te, es+ft-1` present
     `L_p`, and the tensor square adds sixteen commutators.
3. **Conclusion.** `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`(3,4)
   makes each unit group finitely presented, and simple modulo `F_p^x`. A
   finitely presented group modulo a finite central subgroup is finitely
   presented.
