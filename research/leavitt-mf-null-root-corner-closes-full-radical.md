---
rg: 2
id: leavitt-mf-null-root-corner-closes-full-radical
kind: route
title: An MF-null negative-root corner collapses the Leavitt MF radical
target: property-t-free-leavitt-full-mf-radical
requires:
  - leavitt-root-corner-algebra-is-mf-null
  - mf-null-corner-criterion-needs-faithful-ce-trace
  - full-leavitt-idempotent-defect-saturation
---

1. Apply part (A) of `mf-null-corner-criterion-needs-faithful-ce-trace` with `B = P_z C[Delta] P_z` and `Phi` the
   identity. Here `z = x_13(s_1 t_1)` has order two, so `q_z = P_z`. Since `B` is MF-null by
   `leavitt-root-corner-algebra-is-mf-null`, this gives `z in Rad_MF(Delta)`.
2. `full-leavitt-idempotent-defect-saturation` says `z` normally generates `Delta = St_20(L_(F_2)(1,2))`.
3. `Rad_MF(Delta)` is normal, so `Rad_MF(Delta) = Delta`.

No step uses Property `(T)` or any stability input.
