---
rg: 2
id: leavitt-center-is-coefficient-field
kind: claim
title: The center of the binary Leavitt algebra is its coefficient field
distinct_from:
  leavitt-unit-group-has-no-finite-normal-subgroup: that is the group-theoretic conclusion this claim feeds; this is the internal ring-theoretic center calculation.
  binary-leavitt-algebra-not-directly-finite: that is the failure of direct finiteness in the same ring; this identifies its center.
  binary-leavitt-family-lifts-into-unit-corner: that asks for a Leavitt family in a group-algebra corner; this concerns the original coefficient algebra.
artifacts:
  - GroupApproximation/Leavitt/BinaryLeavittSimple.lean
---

**ESTABLISHED INTERNALLY.** For every field `k`, the center of the Leavitt
algebra `L_k(1,2)` is `k`.  In particular,

```text
Z(R)=F_2,                 R=L_(F_2)(1,2),
```

so `Z(R)^x={1}`.  No external center theorem is used.

Write a central element as a finite linear combination of the spanning
monomials `s_alpha t_beta`.  Choose `r` bounding all word lengths and
sandwich by the kill word `W=0^r1`.  Centrality and `t_Ws_W=1` show that the
sandwich fixes the element.  Direct prefix cancellation shows that the
sandwich of every bounded monomial is either zero or one.  Hence the
original element is a scalar.  This needs spanning only, not linear
independence of the monomials.

The Lean declarations `BinaryLeavitt.eq_smul_one_of_central`,
`BinaryLeavitt.center_eq_bot`, and
`BinaryLeavitt.central_units_trivial` implement the calculation for every
field and specialize it to `F_2`.

This supplies the no-nontrivial-central-units input to the internal root
detection proof of `binary-leavitt-elementary-group-is-simple`, as well as
the unit-group applications.

DERIVATION
leavitt-center-kill-word-sandwich-proof
