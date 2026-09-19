---
rg: 2
id: atlas-a8-six-transvection-normal-certificates
kind: claim
title: Six one-conjugate certificates propagate collision 19243 to a generating transvection set of A8
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
---

In the standard chart coordinates `A8 ~= GL_4(F2)`, let

```text
t01,t10,t12,t21,t23,t32
```

be the six adjacent elementary transvections `I+E_(i,j)` with
`(i,j)=(0,1),(1,0),(1,2),(2,1),(2,3),(3,2)`.  The repeated first-chart
syllable `b` of collision `q_19243` is exactly `t23`.

The six transvections generate all of `GL_4(F2)`, of order `20160`.  Moreover,
for every one of the six generators there is a word `a_s` in the same six
transvections such that

```text
s = a_s t23 a_s^-1.                                    (A8-6CERT)
```

The conjugators may be chosen with lengths

```text
8,10,4,6,0,2
```

in the order displayed above; the accompanying exact BFS audit freezes shortest
such words.

Consequently the normal-certificate compiler need not encode a product of many
collision conjugates for any standard chart generator: its maximum collision
multiplicity is

```text
M=1.
```

Only six fixed conjugacy relation words are needed to propagate a small
collision transvection to a generating set for the entire chart group.
