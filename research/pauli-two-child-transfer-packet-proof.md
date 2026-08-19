---
rg: 2
id: pauli-two-child-transfer-packet-proof
kind: route
title: Read the exact branch identities and trace accounting from the Pauli packet
target: pauli-two-child-transfer-packet
requires: []
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
---

The cited exact packet defines

```text
E  = P Q,
T0 = U^* P Q,
T1 = U^* R P Q.
```

Its basis-free Pauli calculation proves

```text
T0^*T0=T1^*T1=E,
(T0T0^*)(T1T1^*)=0,
T0T0^*+T1T1^*=U^*QU.
```

Set `R_i=T_iT_i^*` and `F=U^*QU`.  The same fixed finite regular-character
audit gives

```text
tau(E)=1/8,
tau(F)=1/4.
```

Traciality of each partial isometry gives `tau(R_i)=tau(E)=1/8`.  These are
exact identities in the fixed finite packet, establishing the claim.