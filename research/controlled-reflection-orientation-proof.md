---
rg: 2
id: controlled-reflection-orientation-proof
kind: route
title: Classify marked-spin controller representations and expose the free orientation
target: controlled-reflection-cell-has-free-orientation
requires: []
---

Let `c` commute with all control `Z` operators, all irrelevant `X` operators,
and a system involution `r`, with `cX_jcX_j=r`.  On the marked Pauli spin
sector the Pauli action is irreducible on its spin factor.  Commutation with
`Z_j` makes

```text
c=P_0 tensor u_0+P_1 tensor u_1,
```

where `u_0,u_1` are commuting multiplicity involutions commuting with `r`.
The last controller relation is exactly `u_0u_1=r`; hence

```text
c=P_0 tensor u+P_1 tensor ur
```

for an arbitrary such involution `u`.  The intended controller is only the
choice `u=I`.  After a Hadamard,

```text
P_0HcHP_0=P_0 tensor u(I+r)/2,
```

so the orientation occurs directly in the acceptance corner.

The presentation admits the character twist `c -> -c`, fixing every Pauli
generator and `r`, because every relator contains `c` evenly.  It preserves
the marked spin while sending `u` to `-u`; therefore no condition seeing
only the Pauli central sign can choose the intended orientation.

Completeness is unaffected: for any exact game model, defining
`c_j=P_0+P_1r_j` on fresh control qubits satisfies every controller cell and
gives the exact block encoder.  The obstruction is solely universal
soundness, proving the claim's boundary.
