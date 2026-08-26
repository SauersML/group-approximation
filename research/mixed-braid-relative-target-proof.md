---
rg: 2
id: mixed-braid-relative-target-proof
kind: route
title: Multiply the mixed braid and test its relative word on one signed Hecke root
target: mixed-braid-gauge-cancellation-misses-signed-hecke-targets
requires:
  - mixed-completeness-braid-retains-s3-square-gauge
  - individual-cross-whiteheads-miss-native-hecke-target
---

Write matrices on `(7,8,9)`.  From `(MCB3)`,

```text
G=ABA
 =[[0,  p, 1],
   [r,q_0, r],
   [q_1,0,q_0]],

K=UVU
 =[[q_1,p,0],
   [r,q_0,0],
   [0,  0,1]].                                        (1)
```

Use

```text
pr=q_0,  rp=q_1,  q_0+q_1=1,
p q_0=q_1p=rq_1=q_0r=0.                              (2)
```

Multiplying either `GK` or `KG` gives

```text
[[q_0,0,1],
 [0,  1,r],
 [q_1,0,q_0]].                                        (3)
```

Its square is the identity, proving `(MBT2)`.  Both `L` and `J_1` fix the
second actor coordinate.  Conjugation of `x_28(1)` therefore reads the
eighth row of the inverse transporter.  The eighth row of `L=L^(-1)` is
`(0,1,r)`, which proves `(MBT3)`.

For the native comparison set `g=J_1^(-1)L`.  Since `J_1` is involutive,
`g^(-1)=LJ_1`.  Multiplying `(0,1,r)` on the right by the block `(MBT5)`
gives `(x_1,1-e_00,r)`, proving `(MBT6)`.

Finally, equality of either finite group-algebra projection in `(MBT4)` or
`(MBT7)` would identify the supports of its distinct group elements and
force the corresponding conjugate of `L_0` to equal `L_0`.  Equations
`(MBT3)` and `(MBT6)` contradict this because their `r` coefficient is
nonconstant.  This completes the target test.

For the advertised one-root repair, multiply `(3)` on the left by
`x_89(r)`.  This gives the `(7,9)` block

```text
W=[[q_0,1],[q_1,q_0]]=W_79(1,q_1).                   (4)
```

Conjugating `x_79(1)` uses column seven and row nine of `(4)`.  The two
diagonal coefficients vanish by `q_0q_1=q_1q_0=0`, leaving exactly
`x_79(q_0)x_97(q_1)`.  The eighth coordinate is fixed by `W`, so the
eighth row of `WJ_1` is the eighth row of `J_1`, namely
`(x_1,1-e_00,0)`.  These are the two assertions following `(MBT8)`.
