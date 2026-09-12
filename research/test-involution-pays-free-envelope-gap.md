---
rg: 2
id: test-involution-pays-free-envelope-gap
kind: claim
title: The artificial test-involution defect pays the entire free-envelope generator-diagonal gap
distinct_from:
  generator-diagonal-does-not-couple-to-root-leak: that gives an exact local packet with a positive distinguished gap against an artificial free envelope; this proves quantitatively that violation of the envelope's extra order-two test relation pays that manufactured gap with the sharp constant.
  generator-diagonal-is-a-central-matrix-range-separator: that lower-bounds the diagonal gap from distance to the full SL3 matrix range; this upper-bounds only the gap for the artificial envelope obtained by replacing one infinite-order root coordinate with an involution.
---

Let

```text
K=C_2*F_(m-1)=<r,u_2,...,u_m | r^2=1>,
```

let `x=(B,X_2,...,X_m)` be any `m`-tuple of unitaries in `M_d`, and let
`MR_d(K)` be the ucp matrix range of the displayed canonical generators.
For the distinguished generator diagonal

```text
C=(B,X_2,...,X_m)/sqrt(m),
```

put

```text
Delta(C;x)=Re sum_j tr(C_j^*x_j)
 -sup_(Y in MR_d(K)) Re sum_j tr(C_j^*Y_j).
```

Then

```text
Delta(C;x)<=||B^2-I||_2^2/(4 sqrt(m)).                 (RIG1)
```

The constant is sharp.  In the packet of
`generator-diagonal-does-not-couple-to-root-leak`, `m=6` and `B^2=-I`,
so the right side is `1/sqrt(6)`, exactly the computed diagonal gap.

Here `r^2=1` is an artificial test-envelope relation used to manufacture
the local support gap.  The actual elementary root element `x_21(-1)` in
`SL_3(Z)` has infinite order, so `(RIG1)` is not an arithmetic correction
theorem.  Rather, it diagnoses the countermodel exactly: the entire gap is
paid by the extra order-two test relation.  Any actual `SL_3(Z)`
matrix-range coupling must use genuinely mixed lattice relations, because
the single root coordinate has no torsion relation.  This result does not
identify which mixed relation supplies the required comparison point.

DERIVATION
test-involution-free-envelope-proof
