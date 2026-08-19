---
rg: 2
id: atlas-pauli-recurrence-from-range-packing
kind: route
title: Convert final-range packing costs into the Pauli branch automaton
target: atlas-pauli-branch-recurrence-automaton
requires:
  - atlas-pauli-range-packing-recurrence
  - partial-isometry-leakage-is-range-defect
  - partial-isometry-gram-is-range-overlap
---

Take the fixed state family, word-derived partial isometries and strongly
connected graph supplied by `atlas-pauli-range-packing-recurrence`.  For an
edge `e:i->j`, put `F_e=T_eT_e^*`.  The exact leakage identity gives

```text
||(1-P_j)T_e||_2^2 = tau((1-P_j)F_e)=O(delta^c),
```

which is clause 3 of `atlas-pauli-branch-recurrence-automaton`.

For distinct incoming edges `e,f` at the same target, the exact Gram/range
identity gives

```text
||T_e^*T_f||_2^2=tau(F_eF_f).
```

Summing over ordered pairs turns `(RPR2)` into clause 4.  The source
projections, exact Pauli children, fixed finite state family and strong
connectivity are unchanged.  Hence every clause of the branch-recurrence
target follows.