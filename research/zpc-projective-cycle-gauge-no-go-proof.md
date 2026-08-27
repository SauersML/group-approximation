---
rg: 2
id: zpc-projective-cycle-gauge-no-go-proof
kind: route
title: Gauge a theta graph and place Pauli curvature in its cycle commutant
target: zpc-projective-cycle-gauge-cannot-glue-priority-decoders
requires:
  - odd-selector-priority-decoding
---

Equation `(ZCG2)` is a direct calculation.  For an edge from `c` to `d`,

```text
(S_d T_e S_c^*)(S_c U_c S_c^*)(S_c T_e^* S_d^*)
 =S_d U_d S_d^*.
```

Along a based closed path all intermediate gauges cancel, leaving conjugacy
by the base gauge.  Group-word equations equal to the identity and central
phase equations are invariant under that conjugacy.  Literal distance
between operators at two different vertices plainly has no such invariance.

For the packet amplification statement, gauge a maximal tree first.  Every
chord return then commutes with the represented base overlap algebra.  On
tensoring all vertex spaces with a finite marked representation of the
projective packet, put its generators in the new tensor factor and multiply
the corresponding chord transporters by them.  This changes neither local
operators nor edge covariance and realizes all packet relations.  Common
cross-amplification handles unequal initial multiplicities.

For the sharp model, `(ZCG4)` has odd parity and the priority projections are

```text
Q_(c,1)=I, Q_(c,2)=0,       Q_(d,1)=0, Q_(d,2)=I.
```

Thus the decoded outputs are exactly `(ZCG3)`.  Pauli anticommutation gives
`XZX=-Z`, proving every equation in `(ZCG5)`.  The two relative returns are
as displayed in `(ZCG6)`, and `XZXZ=-I`, so their commutator is the marked
central sign.  Finally

```text
(U_c-U_d)^*(U_c-U_d)=4I,
```

whose normalized trace is `4`.  All asserted defects are identically zero,
so amplification preserves both zero loss and the mismatch.  This proves the
dimension-free impossibility.

