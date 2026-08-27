---
rg: 2
id: sign-cosets-separate-clouds-proof
kind: route
title: Use one column on which two Pauli rows have opposite signs
target: sign-double-cosets-separate-pauli-clouds
requires: []
---

Suppose distinct X clouds `q,q'` occupy the same `H_X` coset.  Choose a Z
cloud `r` on which their tested signs differ, say `b(q,r)=0` and
`b(q',r)=1`.  Moving from the chosen cloud representatives to the actual
pair-edge occurrences multiplies on the X side by `H_X` and on the Z side
by `H_Z`.  Therefore the same relative cloud pair belongs both to

```text
H_X P_0 H_Z             and             H_X P_1 H_Z,
```

contradicting `(SDC1)`.  The column argument is identical with X and Z
reversed.  Nondegeneracy of a binary Pauli pairing supplies the required
separating row or column.

