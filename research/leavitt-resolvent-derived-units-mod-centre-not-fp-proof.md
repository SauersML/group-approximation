---
rg: 2
id: leavitt-resolvent-derived-units-mod-centre-not-fp-proof
kind: route
title: Apply the scalar-commutator obstruction to the rational Leavitt family inside the resolvent ring
target: leavitt-resolvent-derived-units-mod-centre-not-fp
requires:
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
  - leavitt-scalar-commutators-block-fp-central-quotients
---

Lane proof, not independently reviewed.

1. **Q is a central subfield.** By `leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
   part 1, `Q ⊆ R_L` unitally, with `1/m` the inverse of the central element `m·1`.
   The inverse of a central unit is central, so `Q ⊆ Z(R_L)`.
2. **A Leavitt family.** The generators satisfy `t_i s_j = δ_ij` and
   `s_1 t_1 + s_2 t_2 = 1`: these are relators of `R_L`.
3. **Apply the obstruction.** By `leavitt-scalar-commutators-block-fp-central-quotients`,
   parts 1 and 2 with `K = Q` and `d = 2`, where `C_0 = Q^x·1`:
   - `U/C` is not finitely presented for `Q^x ≤ C ≤ Z(U)`;
   - `D/C` is not finitely presented for `Q^x ≤ C ≤ Z(D)`; here `Q^x ≤ Z(D)` since
     it is central in `U` and contained in `L_Q(1,2)^x ≤ D`;
   - `E_N(R_L)` modulo its centre is not finitely presented for `N >= 2`.
4. **The OPEN claim fails.** `leavitt-resolvent-derived-units-mod-centre-fp-simple`
   asserts that `D/Z(D)` is finitely presented (and simple), which contradicts step 3.
