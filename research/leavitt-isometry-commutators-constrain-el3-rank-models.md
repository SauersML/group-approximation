---
rg: 2
id: leavitt-isometry-commutators-constrain-el3-rank-models
kind: claim
title: Leavitt isometry relations impose reversed commutator identities on every characteristic-two rank model of the Leavitt unit group
distinct_from:
  el3-unit-root-matrix-units-iff-two-root-identities: that is the equivalence between the matrix-unit hypothesis and the two single-coefficient identities N_12^2 = 0, N_23 N_12 = 0; this records the operator identities forced by the isometry coefficients t_i, s_j through t_i s_j = delta_ij, which carry no finite-dimensional representation and are the input a proof of the gate must use.
  fd-represented-coefficients-violate-two-root-identities: that shows honest regular-representation models over any finitely represented coefficient ring violate N_23 N_12 = 0; this exhibits the extra relations that hold specifically because the Leavitt coefficients have no finite-dimensional representation.
artifacts:
  - research/artifacts/leavitt-isometry-commutator-relations-2026-09-12.md
---

**ESTABLISHED** (direct computation; proof route
`leavitt-isometry-commutators-proof`). Let `sigma : EL_3(L_(F_2)(1,2)) -> M^x` be a homomorphism
into a characteristic-two rank ultraproduct, and put `n_ab(c) = sigma(x_ab(c)) - 1`,
`A_i = n_12(t_i)`, `B_j = n_23(s_j)`, `Z = n_13(1)`. Then, because `t_i s_j = delta_ij`:

```text
i != j:  A_iB_j + B_jA_i + A_iB_jA_i + B_jA_iB_j + A_iB_jA_iB_j = 0 ;
i = j:   A_iB_i + B_iA_i + A_iB_iA_i + B_iA_iB_i + A_iB_iA_iB_i = Z .
```

Moreover `1 + n_12(1) = (1 + n_12(e_0))(1 + n_12(e_1))` for the orthogonal idempotents
`e_i = s_i t_i`, from `s_0 t_0 + s_1 t_1 = 1`.

These identities use the Leavitt isometry relations directly. Taken **jointly**, the four
relations for `i, j in {0, 1}` force a unital two-pair Cohn family, which has no unital
finite-dimensional representation (`rank(TS) <= n < 2n`). So jointly, by
`fd-represented-coefficients-violate-two-root-identities`, they are not consequences of the group
relations available over any finitely represented coefficient subring. Individually they are:
the diagonal relation alone uses only `t_0 s_0 = 1`, and the Toeplitz subring maps onto `F_2`, so
the Calibration C models satisfy it; an off-diagonal relation alone uses only `t_0 s_1 = 0`, which
holds in `M_2(F_2)` (`t_0 -> E_11`, `s_1 -> E_22`). Jointly they are the type of input
`rank-models-of-el3-satisfy-the-two-root-identities` requires. (Scope sharpened after
`gk-vf-linear`'s pass, Section 41 of its verification artifact.)

**What this does not do.** It does not prove `N_23 N_12 = 0`. The identities carry coefficients
`t_i, s_j`; the target product carries coefficient `1`, and no group-relational bridge from the
coefficient-`1` root elements to the isometry generators is known. See the artifact, Section 1.

## Attempts

Established; the proof is the commutator expansion of the group relations
`[x_12(t_i), x_23(s_j)] = x_13(t_i s_j)` under `sigma`. The open use of these relations toward
the gate is recorded on `rank-models-of-el3-satisfy-the-two-root-identities`.
