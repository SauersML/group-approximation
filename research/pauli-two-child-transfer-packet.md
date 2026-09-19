---
rg: 2
id: pauli-two-child-transfer-packet
kind: claim
title: The atlas Pauli sector contains one exact two-child branching cell
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
---

In the fixed raw/comb Pauli packet of the atlas presentation there are
projections `E,R_0,R_1,F` and partial isometries `T_0,T_1` satisfying

```text
T_i^* T_i = E,
T_i T_i^* = R_i,
R_0 R_1 = 0,
R_0 + R_1 = F,
```

with canonical regular-character traces

```text
tau(E)=tau(R_0)=tau(R_1)=1/8,
tau(F)=1/4.
```

Concretely, on the carrier of `TRUE_PAULI_BRANCH_TRANSFER_PACKET.md`,

```text
E  = P Q,
T0 = U^* P Q,
T1 = U^* R P Q,
F  = U^* Q U.
```

Thus the finite coefficient dynamics already has one genuine branch: the
state `E` emits two orthogonal isometric children of equal positive trace.
No approximation, multiplicity choice, or asymptotic argument is involved in
this cell.  Any remaining nonhyperlinearity proof based on finite-state branch
pressure only has to make these two children recurrent in a low-energy finite
coefficient automaton.