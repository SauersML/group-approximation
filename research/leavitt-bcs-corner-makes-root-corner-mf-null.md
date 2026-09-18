---
rg: 2
id: leavitt-bcs-corner-makes-root-corner-mf-null
kind: route
title: The fixed no-CE BCS corner map makes the Leavitt root corner MF-null
target: leavitt-root-corner-algebra-is-mf-null
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - agent-leavitt-not-bcs-negative-root-corner
  - mf-null-corner-criterion-needs-faithful-ce-trace
---

1. **`A(B_loop)` is CE-null.** Use the BCS dictionary and the strict finite-dimensional synchronous gap, exactly as in
   `agent-leavitt-not-bcs-corner-closes-full-radical`.
2. **So it is MF-null.** This is part (A0) of `mf-null-corner-criterion-needs-faithful-ce-trace`.
3. **So is the corner.** The corner claim gives a unital `Phi : A(B_loop) -> P_z C[Delta] P_z`. The first part of (A)
   then says `P_z C[Delta] P_z` is MF-null.

This route shows the new hole is no harder than the old one. By part (C) of the target claim's criterion, it also
proves that `Delta` is nonhyperlinear.
