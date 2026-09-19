---
rg: 2
id: tight-frame-via-common-negative-carrier
kind: route
title: Equal negative incidence carriers make the defect row automatically tight
target: affine-frobenius-tight-defect-column-frame
requires:
  - affine-frobenius-common-negative-carrier
---

Fix a variable `x` with `r` incidences and write `p=p_x`.  Equation
`(AFNC1)` gives

```text
D_i=(1-A_(c_i,x))q_(c_i,x)=2p                         (TFNC1)
```

for every column.  Hence

```text
DD^*=4r p,
DD^*D=4r D.                                           (TFNC2)
```

Thus `(AFT2)` holds with the positive integer `lambda_x=4r`.  The reflection
`1-2p` proves the compatibility equations, while the packet embeddings and
deficit ledger are part of the required common-carrier claim.  This proves
the tight-defect target.
