---
rg: 2
id: seven-head-star-return-support-proof
kind: route
title: Compute the support and Coxeter word of the seven-head star return
target: seven-head-star-return-retains-eighth-flag
requires:
  - four-cell-marked-star-has-an-eighth-head-flag
---

Use the commuting involution packet

```text
C_1,C_2,C_3,C_4,Z_2,Z_3,Z_4
```

and the conjugation rules `(1)--(2)` of
`four-cell-asymmetric-head-support-proof`.  Direct substitution through
`R_8=H_3H_2H_1H_2H_1H_2H_1` gives

```text
Ad(R_8)(C_1)=C_1Z_2,
Ad(R_8)(C_2)=C_2C_3Z_3Z_4,
Ad(R_8)(C_3)=C_3Z_4,
Ad(R_8)(C_4)=C_4.                                     (1)
```

On `E_4`, where every `C_i=-1`, requiring the four transported centers to
remain negative successively gives

```text
Z_2=+1,                 Z_4=+1,                 Z_3=-1. (2)
```

For the inverse word the same calculation gives

```text
Ad(R_8^(-1))(C_1)=C_1C_2Z_2Z_3,
Ad(R_8^(-1))(C_2)=C_2Z_3,
Ad(R_8^(-1))(C_3)=C_3Z_4,
Ad(R_8^(-1))(C_4)=C_4.                                (3)
```

The inverse transported-center conditions are therefore

```text
Z_2=-1,                 Z_3=+1,                 Z_4=+1. (4)
```

The transported center projections commute with `E_4`, so `(2)` and `(4)`
are exactly the range and source projections of the compressed word.
Pauli balance gives relative rank `1/8` for each, proving `(SHR2)`.

For the separate formal holonomy audit, read the head occurrences from
right to left.  The corresponding adjacent reservoir word is

```text
V_3V_2V_1V_2V_1V_2V_1=V_3(V_2V_1)^3.
```

The involutions `V_1,V_2` satisfy the braid, equivalently
`(V_2V_1)^3=1`, by the literal Whitehead Coxeter packet.  This proves
`(SHR3)` with precisely the scope stated in the claim.  None of these
support calculations asserts that the nonreducing head polar gauges have
already been identified with the Whitehead gauges.
