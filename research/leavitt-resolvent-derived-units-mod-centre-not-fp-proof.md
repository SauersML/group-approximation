---
rg: 2
id: leavitt-resolvent-derived-units-mod-centre-not-fp-proof
kind: route
title: Apply the scalar-commutator obstruction to the rational Leavitt family inside the resolvent ring
target: leavitt-resolvent-derived-units-mod-centre-not-fp
requires:
  - leavitt-resolvent-ring-is-fp-and-contains-q
  - leavitt-scalar-commutators-block-fp-central-quotients
---

Lane proof. Referee PASS: `gq-referee-a` (proof-gap lens, report 58d536cf7) and `gq-referee-b` (citation lens, `research/artifacts/gq-referee-b-leavitt-scalar-commutators-block-fp-central-quotients.md`, c81257d90).

1. **Q is a central subfield.** By `leavitt-resolvent-ring-is-fp-and-contains-q`,
   `R_L ≠ 0` and `Q ⊆ Z(R_L)` as a unital subring. Simplicity of `R_L` is not used.
2. **A Leavitt family.** The same node records that `(s_1, s_2, t_1, t_2)` is a
   Leavitt pair: `t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`. The subalgebra it
   generates over the central `Q` is a copy of `L_Q(1,2)`, which is simple, so the
   map from `L_Q(1,2)` is injective.
3. **Apply the obstruction.** By `leavitt-scalar-commutators-block-fp-central-quotients`,
   parts 1 and 2 with `K = Q` and `d = 2`, where `C_0 = Q^x·1`:
   - `U/C` is not finitely presented for `Q^x ≤ C ≤ Z(U)`;
   - `D/C` is not finitely presented for `Q^x ≤ C ≤ Z(D)`; here `Q^x ≤ Z(D)` since
     it is central in `U` and contained in `L_Q(1,2)^x ≤ D`;
   - `E_N(R_L)` modulo its centre is not finitely presented for `N >= 2`. This bullet
     alone uses `leavitt-gl-equals-el-and-perfect-unit-group`, a repository-internal
     Lean node that the referees did not check; the statements for `U` and `D` do
     not need it.
4. **The OPEN claim fails.** `leavitt-resolvent-derived-units-mod-centre-fp-simple`
   asserts that `D/Z(D)` is finitely presented (and simple), which contradicts step 3.
