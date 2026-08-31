---
rg: 2
id: agent-leavitt-not-bcs-corner-closes-full-radical
kind: route
title: Feed the fixed non-CE BCS through the marked Leavitt root corner
target: property-t-free-leavitt-full-mf-radical
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - agent-leavitt-not-bcs-negative-root-corner
  - agent-leavitt-not-torsion-corner-noce-forces-mf-radical
  - full-leavitt-idempotent-defect-saturation
---

The fixed BCS `B_loop` has a tracial state but no Connes-embeddable tracial
state.  Indeed, the BCS dictionary identifies its perfect commuting strategy
with a tracial state on the same forbidden-joint-projection algebra
`A(B_loop)`.  A Connes-embeddable trace on that algebra would give a perfect
`R^U` model, hence finite-dimensional synchronous strategies with values
tending to one.  This contradicts the strict finite-dimensional synchronous
gap in `lin-explicit-fixed-bcs-gap-via-generic-conversion`.  The corner claim
gives

```text
A(B_loop) -> P_z C[Delta]P_z,       P_z=(1-z)/2,
Delta=St_20(L_(F_2)(1,2)),          z=x_13(s_1t_1).          (LNR1)
```

Apply `agent-leavitt-not-torsion-corner-noce-forces-mf-radical` with the
order-two element `z`.  It gives `z in Rad_MF(Delta)` directly, even if the
coordinate ranks of `P_z` tend to zero relative to the ambient matrices and
even though `z` is noncentral.  Finally
`full-leavitt-idempotent-defect-saturation` says that `z` normally generates
`Delta`.  Normality of the MF radical therefore gives

```text
Rad_MF(Delta)=Delta.                                        (LNR2)
```

Every step after the finite algebraic corner diagram is Property-`(T)`-free.
