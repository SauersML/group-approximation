---
rg: 2
id: pauli-canonical-return-gram-floor-proof
kind: route
title: Both canonical returns are onto the same trace-one-eighth Pauli carrier
target: pauli-canonical-return-gram-floor
requires:
  - pauli-two-child-transfer-packet
  - common-range-isometries-have-maximal-gram-overlap
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
---

The exact packet gives `E^2=E`, `R^2=1`, unitary `U`, and the child range
projections

```text
R_0=U^* E U,
R_1=U^* R E R U.
```

For `A_0=EU`,

```text
A_0^*A_0 = U^* E U = R_0,
A_0A_0^* = E U U^* E = E.
```

For `A_1=ERU`, using that `R` is a self-adjoint involution,

```text
A_1^*A_1 = U^* R E R U = R_1,
A_1A_1^* = E R U U^* R E = E.
```

So both exact returns have common final projection `E`.  Apply
`common-range-isometries-have-maximal-gram-overlap` twice, once in each order:

```text
||A_0^*A_1||_2^2 = tau(E),
||A_1^*A_0||_2^2 = tau(E).
```

Finally `pauli-two-child-transfer-packet` supplies `tau(E)=1/8`.  Since the
recurrence target counts ordered pairs of distinct incoming branches, these
two returns contribute `1/4` before any other edge is added.  Hence their Gram
energy cannot be `O(delta^c)` as `delta -> 0`.