---
rg: 2
id: pauli-canonical-return-gram-floor
kind: claim
title: The canonical inverse/raw Pauli returns pay a fixed incoming Gram floor
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
---

In the exact Pauli two-child packet write

```text
E = P Q,
R_0 = U^* E U,
R_1 = U^* R E R U,
tau(E)=1/8.
```

The two obvious exact return arrows from the child ranges to the original
carrier are

```text
A_0 = E U       : R_0 -> E,
A_1 = E R U     : R_1 -> E.
```

Both are partial isometries onto `E`.  Consequently

```text
||A_0^* A_1||_2^2 = ||A_1^* A_0||_2^2 = 1/8.
```

Thus the ordered-pair incoming Gram energy at `E` is already at least `1/4`.
The three-state automaton obtained by closing both exact Pauli children using
only inverse comb transport and the raw involution cannot satisfy the
vanishing-Gram clause of `atlas-pauli-branch-recurrence-automaton`, even at
zero relator defect.