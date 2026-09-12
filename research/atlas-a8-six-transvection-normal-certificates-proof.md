---
rg: 2
id: atlas-a8-six-transvection-normal-certificates-proof
kind: route
title: Exhaustive GL4(2) BFS certifies generation and shortest conjugators for the collision transvection
target: atlas-a8-six-transvection-normal-certificates
requires:
  - atlas-a4-19243-parabolic-normal-closure
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
---

The audited collision matrix is

```text
b = I+E_(2,3)=t23.
```

The standard-library experiment performs exact arithmetic over `F2`.  Starting
from the identity, breadth-first search using

```text
t01,t10,t12,t21,t23,t32
```

visits exactly `20160` matrices, hence the six transvections generate
`GL_4(F2)=A8`.

The same exhaustive table is then scanned for a shortest `a` satisfying

```text
a b a^-1 = s
```

for each of the six targets.  It returns the frozen words

```text
t01: t12 t21 t10 t01 t23 t32 t21 t12

t10: t01 t10 t12 t21 t10 t01 t23 t32 t21 t12

t12: t23 t32 t21 t12

t21: t12 t21 t23 t32 t21 t12

t23: 1

t32: t23 t32.
```

A final exact matrix multiplication pass re-evaluates every displayed identity
and asserts equality.  Thus each standard generator is one conjugate of the
collision transvection, with maximum conjugator length ten and collision
multiplicity exactly one.
